# Dowker persistence of two cell populations

Let $U$ and $V$ be finite point clouds, for example the positions of two cell types (tumor cells and macrophages) in a tissue image, and let $d(u, v)$ be the distance between $u \in U$ and $v \in V$. For $\varepsilon \ge 0$ the **Dowker complex** $D^{\varepsilon}_{U,V}$ is the simplicial complex on the potential vertex set $U$ whose simplices are the nonempty $\{u_0, \dots, u_k\} \subseteq U$, singletons included, for which some single $v \in V$ satisfies $d(u_j, v) \le \varepsilon$ for all $j$; so its vertices are only the witnessed points of $U$. The complexes are nested in $\varepsilon$ and form the **Dowker filtration** $D^{\bullet}_{U,V}$; $D^{\bullet}_{V,U}$ is defined symmetrically with potential vertex set $V$ and witnesses in $U$. Over a field, the persistent homology of a finite filtration decomposes uniquely into interval modules, whose birth-death pairs form the persistence diagram $\mathrm{pd}_k$.

**Theorem (functorial Dowker theorem).** For every $k$,

$$\mathrm{pd}_k\big(D^{\bullet}_{U,V}\big) = \mathrm{pd}_k\big(D^{\bullet}_{V,U}\big).$$

At each fixed $\varepsilon$ (Dowker's theorem) the geometric realizations of $D^{\varepsilon}_{U,V}$ and $D^{\varepsilon}_{V,U}$ are homotopy equivalent; the functorial version states that these equivalences commute with the inclusions of the filtration, so the persistence modules are isomorphic.

**Construction.** Given the $|U| \times |V|$ distance matrix with $|U| = n$, $|V| = m$, sorting each column $v$ lists the $u$ in order of distance to $v$; the prefixes of the sorted column are the maximal simplices witnessed by $v$ together with their entry values, so the filtered Dowker complex is generated in $O(mn \log n)$ time.

## Expansion

Both complexes are nerves of the same relation $\{(u, v) : d(u, v) \le \varepsilon\}$, read from its two sides, and Dowker's homotopy equivalence is natural in the relation; this naturality is what gives equality of persistence diagrams. The Dowker diagram is therefore a genuinely relational, symmetric summary: $\mathrm{pd}_0$ records at which proximity scales groups of $U$-cells become linked through shared nearby $V$-cells, and points far from the diagonal in $\mathrm{pd}_1$ record loops present in both populations, such as a ring of macrophages around a ring of tumor cells. It is sensitive to outliers of one population lying inside the other. In synthetic agent-based tumor microenvironments, persistence-image vectorizations of the six pairwise Dowker diagrams among tumor cells, macrophages and blood vessels predicted the dominant macrophage phenotype better than single-population Vietoris-Rips features.

## Sources

- B. J. Stolz, J. Dhesi, J. A. Bull, H. A. Harrington, H. M. Byrne, I. H. R. Yoon, "Relational Persistent Homology for Multispecies Data with Application to the Tumor Microenvironment", Bulletin of Mathematical Biology (2024), Section 3 (Definitions 1-3, Theorem 1), Section 4 (Definition 4, Theorem 2, Dowker filtration construction; Definitions 5-6, multispecies witness filtration), Section 5 (tumor microenvironment applications). <https://doi.org/10.1007/s11538-024-01353-6> (PMC11408586)
