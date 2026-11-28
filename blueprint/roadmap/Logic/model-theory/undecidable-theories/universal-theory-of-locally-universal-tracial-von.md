# The universal theory of a locally universal tracial von Neumann algebra is not computable

In continuous logic, the universal theory of any tracial von Neumann algebra into whose ultrapower every separable tracial von Neumann algebra embeds is not computable; consequently no such algebra has a computable presentation.

**Setting.** Tracial von Neumann algebras are treated as metric structures in continuous first-order logic, in the language of tracial von Neumann algebras (operator-norm balls, the algebra operations, the adjoint and the trace). A sentence $\sigma$ takes a real value $\sigma^{\mathcal N}$ in each algebra $\mathcal N$; a *universal* sentence has the form $\sup_{\bar x}\varphi(\bar x)$ with $\varphi$ quantifier-free. The *universal theory* of $\mathcal N$ is the function $\sigma\mapsto\sigma^{\mathcal N}$ on universal sentences, and it is *computable* if there is an algorithm that, given a restricted universal sentence (a universal sentence built from atomic formulas using only continuous connectives from a computable dense set that includes truncated subtraction $a \mathbin{\dot-} b = \max(a - b, 0)$ and rational scalings; Section 2 of the source) and a precision (Definition 2.1), outputs a rational approximation of $\sigma^{\mathcal N}$ within that precision. A tracial von Neumann algebra $\mathcal S$ is *locally universal* if every separable tracial von Neumann algebra embeds in an ultrapower of $\mathcal S$. Such algebras exist (Farah, Hart and Sherman), and all of them have the same universal theory, with $\sigma^{\mathcal S}=\sup_{\mathcal N}\sigma^{\mathcal N}$ over all separable $\mathrm{II}_1$ factors $\mathcal N$.

**Theorem (Arulseelan and Manzoor).** The universal theory of any locally universal tracial von Neumann algebra is not computable. Consequently, no locally universal tracial von Neumann algebra admits a computable presentation.

By the Pavelka-style completeness theorem of continuous logic, $\sup_{\mathcal N}\sigma^{\mathcal N}$ is also the infimum of the rationals $r$ for which the theory of tracial von Neumann algebras proves $r\ge\sigma$, so this value cannot be approximated by any algorithm. The hyperfinite $\mathrm{II}_1$ factor is not locally universal, by the negative solution of the Connes embedding problem (Ji, Natarajan, Vidick, Wright and Yuen; see [the refutation of the Connes embedding conjecture](../../../QuantumInformation/quantum-foundations/tsirelson-problem-and-connes-embedding/refutation-of-the-connes-embedding-conjecture.md)); the theorem concerns the algebras that are.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof combines Lin's theorem $\mathrm{MIP}^{\mathrm{co}}=\mathrm{coRE}$ (a preprint, as the source cites it) with an encoding of non-local games as universal sentences: for each Turing machine $M$ there is an effectively computable universal sentence $\sigma_M$ such that $\sup_{\mathcal N}\sigma_M^{\mathcal N}=1$ when $M$ does not halt, and $\sup_{\mathcal N}\sigma_M^{\mathcal N}$ is at most $1/2$ when $M$ halts. If the universal theory of a locally universal $\mathcal S$ were computable, one could compute an interval of length less than $1/8$ containing $\sigma_M^{\mathcal S}=\sup_{\mathcal N}\sigma_M^{\mathcal N}$ and decide from it whether $M$ halts, contradicting the undecidability of the halting problem. Since $\mathcal S$ has a weakly effectively enumerable universal theory, a computable presentation would make that theory computable. A good expansion links pages for $\mathrm{MIP}^{\mathrm{co}}=\mathrm{coRE}$ and for the encoding of non-local games as universal sentences.

## Sources

- J. Arulseelan and A. Manzoor, "The universal theory of locally universal tracial von Neumann algebras is not computable", *International Mathematics Research Notices* 2026(7), article rnag060, 2026, doi:[10.1093/imrn/rnag060](https://doi.org/10.1093/imrn/rnag060); read in arXiv:2508.21709v2 ([arXiv](https://arxiv.org/abs/2508.21709v2)): the definition of local universality and Theorems 4.2 and 4.3 with their proofs in the subsection "Locally Universal Models" of Section 4, the remarks after them, and Definition 2.1 (computable theories).
