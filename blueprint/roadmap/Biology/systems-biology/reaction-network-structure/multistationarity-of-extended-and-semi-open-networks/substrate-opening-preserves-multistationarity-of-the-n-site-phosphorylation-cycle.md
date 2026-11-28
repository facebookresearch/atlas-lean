# Substrate opening preserves multistationarity of the n-site phosphorylation cycle

Let $\mathcal{P}^n$ be the sequential distributive $n$-site double phosphorylation cycle under mass-action kinetics, with substrates $S_0,\dots,S_n$, kinase $E$, phosphatase $F$ and enzyme-substrate complexes:

$$S_i + E \rightleftharpoons ES_i \to S_{i+1} + E, \qquad S_{i+1} + F \rightleftharpoons FS_{i+1} \to S_i + F, \qquad 0 \le i \le n-1.$$

A species $X$ is *opened* by adding the inflow and outflow reactions $0 \to X$ and $X \to 0$; for a set $\mathcal{S}$ of species, $\mathcal{P}^n_{\mathcal{S} \rightleftharpoons 0}$ denotes the resulting semi-open network (a partially open continuous-flow stirred-tank model). A network *admits nondegenerate multistationarity* if, for some positive rate constants, some stoichiometric compatibility class contains at least two positive steady states $x^*$ with $\ker Jf(x^*) \cap S = \{0\}$. Write $\operatorname{cap}_{pos}(G)$ for the maximal number of isolated positive steady states in a compatibility class over all rate constants.

**Theorem.** For every $n \ge 2$ and every subset $\mathcal{S} \subseteq \{S_0,\dots,S_n\}$ of substrates, $\mathcal{P}^n_{\mathcal{S} \rightleftharpoons 0}$ admits nondegenerate multistationarity; in particular $\operatorname{cap}_{pos}(\mathcal{P}^n_{\mathcal{S} \rightleftharpoons 0}) \ge 2$.

So the bistable switch of multisite phosphorylation survives exchange of any collection of substrate forms with a reservoir (synthesis and degradation of the substrate in any phosphoform).

## Depends on

- [Maximal multistationarity of multisite phosphorylation](../../chemical-reaction-network-theory/maximal-multistationarity-of-multisite-phosphorylation.md)
- [Lifting nondegenerate multistationarity to networks with intermediates](lifting-nondegenerate-multistationarity-to-networks-with-intermediates.md)

## Expansion

The proof is an induction on $n$. The base case $n = 2$ with one opened substrate is checked directly by exhibiting rate constants with several nondegenerate steady states. For the step, a nondegenerate positive steady state of $\mathcal{P}^n_{S_i \rightleftharpoons 0}$ is extended to a positive steady state of the network with one more site, and the extension is shown to remain nondegenerate, so nondegenerate multistationarity passes from $\mathcal{P}^n_{S_i \rightleftharpoons 0}$ to $\mathcal{P}^{n+1}_{S_i \rightleftharpoons 0}$. The case of the newly added fully phosphorylated form follows from a symmetry: relabeling sites by the number of unphosphorylated residues and swapping $E$ with $F$ shows that $\mathcal{P}^n_{S_i \rightleftharpoons 0}$ and $\mathcal{P}^n_{S_{n-i} \rightleftharpoons 0}$ are dynamically equivalent. Finally, once one substrate is open, opening further substrates does not change the stoichiometric subspace, and enlarging a network without changing its stoichiometric subspace preserves nondegenerate multistationarity (Joshi-Shiu); this gives the statement for every nonempty $\mathcal{S}$.

## Sources

- Praneet Nandan, Beatriz Pascual-Escudero, Diego Rojas La Luz, "Multistationarity in semi-open Phosphorylation-Dephosphorylation Cycles", *Bulletin of Mathematical Biology* 88(11) (2026), 217, Definitions 2.5 and 2.11, Theorem 3.1, Proposition 3.3, Theorem 3.4, Lemmas 3.5 and 3.6, Theorem 3.7, <https://doi.org/10.1007/s11538-026-01771-8> (preprint arXiv:2511.10609).
