# Naturality of the dual comparison

Let $C$ and $D$ be monoidal categories and $F : C \to D$ a strong monoidal functor, with unit map $\varepsilon$ and tensor comparison $\mu$ with inverse $\delta$. For an object $X$ of $C$ with a chosen right dual $X^\vee$ such that $FX$ also has a chosen right dual $(FX)^\vee$ (rigidity of the whole categories is not assumed), the image of the exact pairing of $X$ and $X^\vee$ is an exact pairing of $FX$ and $F(X^\vee)$, with coevaluation $\mathrm{coev}_{\mathrm{mapped}} = \varepsilon ; F(\mathrm{coev}_X) ; \delta_{X, X^\vee}$. Let $f : X \to Y$, where $Y$ and $FY$ also have chosen right duals. With the [dual comparisons](map-right-dual-iso.md) $c_X, c_Y$ and the dual maps $f^\vee : Y^\vee \to X^\vee$ and $(Ff)^\vee : (FY)^\vee \to (FX)^\vee$,

$$F(f^\vee) ; c_X.\mathrm{hom} = c_Y.\mathrm{hom} ; (Ff)^\vee.$$

This is the image-pairing construction of Etingof–Gelaki–Nikshych–Ostrik, *Tensor Categories*, Exercise 2.10.6 (the book calls this evaluation order a left dual).
