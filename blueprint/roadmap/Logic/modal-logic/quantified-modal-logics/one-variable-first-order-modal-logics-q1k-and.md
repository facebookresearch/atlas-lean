# One-variable first-order modal logics Q¹K and Q¹S5

$\mathsf{Q^1K}$ and $\mathsf{Q^1S5}$ are the one-variable fragments of first-order modal logic over constant-domain Kripke models, for all frames and for frames with universal accessibility, together with the notions of conservative extension and uniform interpolant relative to a signature.

**Formulas.** Formulas of the one-variable fragment are built from unary predicate symbols $p(x)$ and the single individual variable $x$ using $\top$, $\neg$, $\wedge$, $\exists x$ and $\Diamond$; $\forall x$ and $\Box$ are abbreviations. The *signature* $\mathrm{sig}(\varphi)$ is the finite set of predicate symbols in $\varphi$.

**Models.** A constant-domain model $\mathfrak{M} = (W, R, D, I)$ has a nonempty set $W$ of worlds, $R \subseteq W \times W$, a nonempty domain $D$ and interpretations $p^{I(w)} \subseteq D$. Truth $\mathfrak{M}, w, d \models \varphi$ is defined by $\mathfrak{M}, w, d \models p(x)$ iff $d \in p^{I(w)}$, $\mathfrak{M}, w, d \models \exists x\,\varphi$ iff $\mathfrak{M}, w, d' \models \varphi$ for some $d' \in D$, and $\mathfrak{M}, w, d \models \Diamond\varphi$ iff $\mathfrak{M}, w', d \models \varphi$ for some $w'$ with $(w, w') \in R$. $\mathsf{Q^1K}$ is the set of formulas true at every $(w,d)$ of every model, and $\mathsf{Q^1S5}$ the set of those true in all models with $R = W \times W$. For $L$ one of these, $\models_L \varphi$ means $\varphi \in L$.

**Conservative extensions and uniform interpolants.** $\varphi$ is an *$L$-conservative extension* of $\psi$ if $\models_L \varphi \to \psi$ and, for every $\chi$ with $\mathrm{sig}(\chi) \subseteq \mathrm{sig}(\psi)$, $\models_L \varphi \to \chi$ entails $\models_L \psi \to \chi$; it is a *strong* conservative extension if this is so for every $\chi$ with $\mathrm{sig}(\chi) \cap \mathrm{sig}(\varphi) \subseteq \mathrm{sig}(\psi)$. The (strong) conservative extension problem, (S)CEP, asks whether a given $\varphi$ is a (strong) conservative extension of a given $\psi$. For a signature $\sigma$, $\chi$ is a *$\sigma$-uniform interpolant* of $\varphi$ in $L$ if $\mathrm{sig}(\chi) = \sigma$ and $\varphi$ is a strong $L$-conservative extension of $\chi$. The uniform interpolant existence problem, UIEP, asks, given $\varphi$ and $\sigma$, whether $\varphi$ has a $\sigma$-uniform interpolant in $L$.

## Depends on

- [Quantified modal logic QL](quantified-modal-logic-ql.md)
- [Kripke model](../kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Expansion

$\mathsf{Q^1S5}$ is closely linked to the two-variable fragment of first-order logic without equality, which lets results transfer between them. None of the first-order modal logics between $\mathsf{K}$ and $\mathsf{S5}$ with constant domains has the Craig interpolation property, even with one variable, which is why existence of interpolants, conservative extensions and uniform interpolants becomes a decision problem. If $L$ has Craig interpolation, conservative and strong conservative extensions coincide.

## Sources

- Agi Kurucz, Frank Wolter and Michael Zakharyaschev, "Deciding the existence of interpolants and definitions in first-order modal logic", *Logical Methods in Computer Science* 21(4):6, 2025, doi:10.46298/lmcs-21(4:6)2025; read as arXiv:2303.04598v4, <https://arxiv.org/abs/2303.04598v4>: Section 2 (the one-variable fragment, constant-domain models, $\mathsf{Q^1K}$ and $\mathsf{Q^1S5}$) and Section 3 (conservative extensions, strong conservative extensions, uniform interpolants and the UIEP) of arXiv:2303.04598v4.
