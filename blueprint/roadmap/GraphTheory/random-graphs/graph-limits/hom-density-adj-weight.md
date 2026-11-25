# Homomorphism density counts homomorphisms

For simple graphs $F$ and $G$ on finite vertex sets,

$$t(F, w_G) = \frac{\hom(F, G)}{\lvert V(G)\rvert^{\lvert V(F)\rvert}},$$

where $\hom(F, G)$ is the number of graph homomorphisms $F \to G$ and $t(F, w_G)$ is the [homomorphism density](hom-density.md) of $F$ in the $0/1$ [weighted graph](adj-weight.md) of $G$. When $G$ has no vertices and $F$ has some, both sides are $0$: there are no maps, and $0/0$ is read as $0$.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, §2.1: for unweighted $G$, $t(F, G) = \hom(F, G) / |V(G)|^{|V(F)|}$.
