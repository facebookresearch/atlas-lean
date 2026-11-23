# The shortest credible prefix has minimum size

Let $\iota$ be a finite set with $m$ elements, let $\alpha : \iota \to \mathbb{R}$, and let $\sigma : \{0, \dots, m-1\} \to \iota$ be a bijection such that $i \mapsto \alpha_{\sigma(i)}$ is nonincreasing. Let $\rho \in \mathbb{R}$ and let $k$ be a natural number such that no [prefix](sorted-prefix.md) $\mathrm{Pre}_\sigma(m')$ with $m' < k$ is a [$\rho$-credible set](is-credible-set.md). Then every $\rho$-credible set $S \subseteq \iota$ has at least $k$ elements (Maller et al. 2012; Wang et al. 2020).

## Sources

- J. B. Maller et al., *Bayesian refinement of association signals for 14 loci in 3 common diseases*, Nat. Genet. 44 (2012), 1294–1301.
- G. Wang, A. Sarkar, P. Carbonetto, M. Stephens, *A simple new approach to variable selection in regression, with application to genetic fine mapping*, J. R. Stat. Soc. B 82 (2020), 1273–1300.
