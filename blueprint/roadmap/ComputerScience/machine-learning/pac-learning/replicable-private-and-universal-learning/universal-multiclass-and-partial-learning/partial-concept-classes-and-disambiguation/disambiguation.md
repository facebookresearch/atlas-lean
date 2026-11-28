# Disambiguations of partial concept classes

A total class $\bar H \subseteq \{0,1\}^X$ **disambiguates** a partial class $H \subseteq \{0,1,\star\}^X$ if every finite labelled sample realizable by $H$ is also realizable by $\bar H$. It **strongly disambiguates** $H$ if every $h \in H$ has an extension $\bar h \in \bar H$ (that is, $\bar h(x) = h(x)$ whenever $h(x) \ne \star$). A strong disambiguation is a disambiguation; every PAC learner for a disambiguation $\bar H$ is a PAC learner for $H$, so a disambiguation of finite VC dimension would reduce learning $H$ to learning a total class. The two notions coincide when every $h \in H$ has finite support, in particular when $X$ is finite.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Definition 9, Theorem 1 and the remarks after Definition 9.
