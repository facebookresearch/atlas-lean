# Separated morphisms of the Int construction

Let $C$ be a symmetric monoidal category with a symmetric trace $T$, and let $\mathrm{Int}(T)$ be its [Int construction](../the-int-construction/README.md): its objects are pairs $X = (X^+, X^-)$ of objects of $C$, and a morphism $X \to Y$ is a morphism $X^+ \otimes Y^- \to Y^+ \otimes X^-$ of $C$. For objects $X$ and $Y$ of $\mathrm{Int}(T)$ and morphisms $f : X^+ \to Y^+$ and $g : Y^- \to X^-$ of $C$, the separated morphism $X \to Y$ is

$$f \otimes g : X^+ \otimes Y^- \to Y^+ \otimes X^-.$$

No symmetry is applied: it is the direction of $g$, from $Y^-$ to $X^-$, that is reversed, not the order of the factors.
