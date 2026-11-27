# Computable elements of the PCF model

Enumerate the finite elements $e^\sigma_0, e^\sigma_1, \dots$ of each domain $D_\sigma$ of the standard model of [PCF](pcf-with-the-parallel-conditional.md):

- at type $o$, $e^o_0 = \bot$, $e^o_1 = \mathit{tt}$ and $e^o_n = \mathit{ff}$ for $n \ge 2$; at type $\iota$, $e^\iota_0 = \bot$ and $e^\iota_{n+1} = n$;
- at $\sigma = (\sigma_1, \dots, \sigma_n, \tau)$ with $\tau$ ground, write $m = \sum_{i \in I} 2^{m_i}$ for the finite set $I$ of positions of the bits set in $m$; each $m_i$ codes
  an $(n+1)$-tuple of indices of finite elements $e_1, \dots, e_n, d$ of $\sigma_1, \dots, \sigma_n, \tau$, and so a step function $(e_1 \Rightarrow \cdots (e_n \Rightarrow d) \cdots)$. The code $m$
  denotes the least upper bound of this finite set $F'$ of step functions when $F'$ satisfies the two conditions that characterize finite elements: every output $d$
  is not $\bot$, and two steps whose inputs $e_i, e_i'$ are pairwise compatible have the same output. Otherwise $m$ is *trivial* and denotes $\bot$. (A set with an upper bound
  can fail the first condition, for example $\{\bot \Rightarrow \bot, \bot \Rightarrow \mathit{tt}\}$, whose join is not $\bot$.)

The order between coded elements, their compatibility and their joins are primitive recursive in the indices. An element $x \in D_\sigma$ is *computable* if
$\{n : e^\sigma_n \sqsubseteq x\}$ is recursively enumerable; equivalently, $x$ is the least upper bound of a chain $e^\sigma_{n_0} \sqsubseteq e^\sigma_{n_1} \sqsubseteq \cdots$ with
$n_0, n_1, \dots$ primitive recursive. Every closed term of PCF, with or without the parallel conditional, denotes a computable element. (Under an arbitrary
environment a free variable may denote a non-computable element, so the restriction to closed terms matters.)

## Depends on

- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)
- [Finite elements are definable in PCF with the parallel conditional](finite-elements-are-definable-with-parallel.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 4, the conditions (1) and (2) on finite elements after Lemma 4.4 on page 239; Section 5, the coding of finite elements and trivial codes and the definition of computable elements on page 249, and the argument there that every $\mathcal{L}_{PA}$-definable element is computable.
