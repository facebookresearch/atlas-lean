# Computable elements of the PCF model

Enumerate the finite elements $e^\sigma_0, e^\sigma_1, \dots$ of each domain $D_\sigma$ of the standard model of [PCF](pcf-with-the-parallel-conditional.md):

- at type $o$, $e^o_0 = \bot$, $e^o_1 = \mathit{tt}$ and $e^o_n = \mathit{ff}$ for $n \ge 2$; at type $\iota$, $e^\iota_0 = \bot$ and $e^\iota_{n+1} = n$;
- at $\sigma = (\sigma_1, \dots, \sigma_n, \tau)$, a number $m = \sum_{i \ge 0} 2^{m_i}$ codes the least upper bound of the finite set of step functions coded by the $m_i$,
  each a tuple of indices of finite elements of $\sigma_1, \dots, \sigma_n, \tau$, when that set has an upper bound, and codes $\bot$ otherwise.

The order between coded elements, their compatibility and their joins are primitive recursive in the indices. An element $x \in D_\sigma$ is *computable* if
$\{n : e^\sigma_n \sqsubseteq x\}$ is recursively enumerable; equivalently, $x$ is the least upper bound of a chain $e^\sigma_{n_0} \sqsubseteq e^\sigma_{n_1} \sqsubseteq \cdots$ with
$n_0, n_1, \dots$ primitive recursive. Every term of PCF, with or without the parallel conditional, denotes a computable element.

## Depends on

- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)
- [Finite elements are definable in PCF with the parallel conditional](finite-elements-are-definable-with-parallel.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 5, the coding of finite elements and the definition of computable elements on pages 248–249, and the argument there that every $\mathcal{L}_{PA}$-definable element is computable.
