# Footprints are exactly the essential states of complete specifications

A state is a footprint of a local function if and only if it lies in the domain of every complete specification of that function. Consequently the footprints are contained in every basis of the function.

Let $f$ be a local function on a separation algebra $\Sigma$, with [footprints](footprints-of-local-functions.md) $F(f)$, and let $\Phi_{\mathrm{comp}}(f)$ be its set of [complete specifications](complete-specifications.md). For every $\sigma \in \Sigma$,

$$F_f(\sigma) \iff \sigma \in D(\varphi) \text{ for every } \varphi \in \Phi_{\mathrm{comp}}(f).$$

Moreover, for $A \subseteq \Sigma$ and $\varphi_{A,f} = \{(\{\sigma\}, f(\sigma)) : \sigma \in A,\ f(\sigma) \neq \top\}$, the set $A$ is a basis for $f$ if and only if $\varphi_{A,f}$ is complete for $f$; hence $F(f) \subseteq A$ for every basis $A$ of $f$.

## Depends on

- [Complete specifications of local functions](complete-specifications.md)
- [Footprints of local functions](footprints-of-local-functions.md)

## Proof depends on

- [Complete specifications of local functions](complete-specifications.md)
- [Footprints of local functions](footprints-of-local-functions.md)
- [Soundness of consequence between specifications](soundness-of-consequence-between-specifications.md)

## Expansion

If some complete $\varphi$ omits $\sigma$ from its domain, then $f = \mathrm{bla}[\varphi]$ and each term of the meet defining $\mathrm{bla}[\varphi]\!(\sigma)$ comes from a strict substate $\sigma_1 \prec \sigma$ lying in a precondition $p$ with $f(\sigma_1) \sqsubseteq q$, so $L_f(\sigma) \sqsubseteq f(\sigma)$ and $\sigma$ is not a footprint. Conversely, if $\sigma$ is not a footprint and $f(\sigma) \neq \top$, removing $(\{\sigma\}, f(\sigma))$ from the big specification keeps it complete: framing the singleton statements of the strict substates $\sigma' \prec \sigma$ with $f(\sigma') \neq \top$, at least one of which exists, and intersecting them derives $(\{\sigma\}, L_f(\sigma)) = (\{\sigma\}, f(\sigma))$; [soundness of consequence between specifications](soundness-of-consequence-between-specifications.md) turns the derivation into semantic consequence. If $f(\sigma) = \top$ the big specification already omits $\sigma$. The basis characterization is $L_{A,f} = \mathrm{bla}[\varphi_{A,f}]$ together with the characterization of completeness by best local functions.

## Sources

- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 4, Theorem 4.7 and its proof; Section 5.1, Lemmas 5.3 and 5.4 (numbers from arXiv:0903.1032v2).
