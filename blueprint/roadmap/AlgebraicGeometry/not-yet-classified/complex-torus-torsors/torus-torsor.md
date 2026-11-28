# Torus Torsor

A $\mathbb{G}_m$-torsor structure on $q : X \to Y$ for the action $A$ of $\mathbb{G}_m$ on $X$
(schemes over $\mathbb{C}$): a continuous action of $\mathbb{C}^\times$ on the space of complex
points of $X$ (`mulAction`, `continuousAction`) under which $g \cdot x$ is the image of $(g, x)$
under the action morphism of $A$ (`compatibility`); and the conditions that $q$ is invariant,
$q(g \cdot x) = q(x)$ as morphisms $\mathbb{G}_m \times X \to Y$ (`invariant`), that the morphism
$\mathbb{G}_m \times X \to X \times_Y X$, $(g, x) \mapsto (x, g \cdot x)$, is an isomorphism
(`relationIso`), and that $q$ is smooth and surjective (`smooth`, `surjective`).
