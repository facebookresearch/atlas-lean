# Norm trick for modular forms

Let $\mathcal{G}$ and $\mathcal{H}$ be subgroups of $\mathrm{GL}_2(\mathbb{R})$ such that
$\mathcal{G} \cap \mathcal{H}$ has finite index in $\mathcal{H}$ and $\det h = \pm 1$ for every
$h \in \mathcal{H}$; neither group need contain the other. Let $k$ be an integer, write
$F|_k g$ for the weight-$k$ slash action of $g \in \mathrm{GL}_2(\mathbb{R})$ on functions $F$ on
the upper half-plane $\mathbb{H}$, and let $d = [\mathcal{H} : \mathcal{G} \cap \mathcal{H}]$.
For a modular form $f$ of weight $k$ for $\mathcal{G}$, its norm to $\mathcal{H}$ is the function

$$N_{\mathcal{H}}(f) = \prod_{q \in \mathcal{H}/(\mathcal{G} \cap \mathcal{H})} f|_k h_q^{-1}$$

on $\mathbb{H}$, where $h_q \in \mathcal{H}$ is any representative of the left coset $q$ (the factor
does not depend on the choice, since $f$ is invariant under $\mathcal{G}$); it is a modular form of
weight $kd$ for $\mathcal{H}$.

Let $F$ and $G$ be modular forms of weight $k$ for $\mathcal{G}$ such that
$(F|_k h) \, G = F \, (G|_k h)$ for every $h \in \mathcal{H}$. Then there is a modular form $\Phi$ of
weight $kd$ for $\mathcal{H}$ with $\Phi \, G = F \, N_{\mathcal{H}}(G)$.
