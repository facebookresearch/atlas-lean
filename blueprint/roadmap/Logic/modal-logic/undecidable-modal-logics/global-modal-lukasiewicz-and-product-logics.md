# Global modal Łukasiewicz and product logics are not recursively enumerable

Global consequence in Kripke models valued in the standard Łukasiewicz algebra, or in the standard product algebra, is not recursively enumerable: no recursive axiomatization of these modal many-valued logics exists.

**Theorem (Vidal).** Let $\vdash_{K\L}$ and $\vdash_{K\Pi}$ be the [global consequence relations](global-modal-many-valued-logics.md) between finite sets of modal formulas and formulas over all safe Kripke models valued in the standard MV-algebra $[0,1]_{\L}$ ($a \cdot b = \max\{0, a + b - 1\}$, $a \to b = \min\{1, 1 - a + b\}$) and in the standard product algebra $[0,1]_\Pi$ ($a \cdot b = ab$, $a \to b = 1$ if $a \le b$ and $b/a$ otherwise), respectively. The sets $\{(\Gamma, \varphi) \mid \Gamma \vdash_{K\L} \varphi\}$ and $\{(\Gamma, \varphi) \mid \Gamma \vdash_{K\Pi} \varphi\}$, with $\Gamma$ finite, are not recursively enumerable; hence neither logic is recursively axiomatizable. The same holds for global consequence over finite models only, $\vdash_{\omega K\L}$ and $\vdash_{\omega K\Pi}$ (Corollary 4.4 of the source).

Whether these consequence relations are $\Pi^0_2$-complete, like the tautologies of first-order Łukasiewicz and product logics, is left open in the source.

## Depends on

- [Global modal many-valued logics are undecidable](global-modal-many-valued-logics.md)

## Proof depends on

None.

## Expansion

*Finite models.* If the propositional consequence of the algebras is decidable, as for Łukasiewicz and product logic, then non-consequence over finite models is recursively enumerable: enumerate finite models and check each (Lemma 4.3). Were $\vdash_{\omega K\L}$ also recursively enumerable, it would be decidable, contradicting the undecidability theorem; so it is not (Corollary 4.4).

*All models.* Using the witnessed-model completeness of first-order Łukasiewicz logic (Hájek), a recursive translation adds to $\Gamma$ and $\varphi$ formulas $\Xi(p)$, $\xi(p, q)$, $\psi(p, q)$ in two fresh variables that force the relevant worlds to have finite height, so that $\Gamma \vdash_{\omega K\L} \varphi$ iff $\Gamma, \Xi(p), \xi(p, q) \vdash_{K\L} \varphi \vee \psi(p, q)$ (Lemma 4.7). An enumeration of $\vdash_{K\L}$ would therefore enumerate $\vdash_{\omega K\L}$ (Theorem 4.8). For product logic, the isomorphism between $[0,1]_{\L}$ and the restriction of $[0,1]_\Pi$ to an interval $[a, 1]$ gives a recursive reduction of $\vdash_{K\L}$ to $\vdash_{K\Pi}$ (Lemma 4.9, Corollary 4.10).

## Sources

- A. Vidal, "Undecidability and non-axiomatizability of modal many-valued logics", *The Journal of Symbolic Logic* 87(4):1576–1605, 2022, <https://doi.org/10.1017/jsl.2022.32>; numbers from arXiv:2101.08767v2, <https://arxiv.org/abs/2101.08767v2>: Section 4: Lemma 4.3, Corollary 4.4, Lemma 4.7, Theorem 4.8, Lemma 4.9 and Corollary 4.10.
