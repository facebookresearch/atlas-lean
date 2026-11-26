# Steady-state invariants of glued reaction networks

A reaction network $N = (\mathcal{S}, \mathcal{C}, \mathcal{R})$ with species concentrations $x = (x_1, \dots, x_n)$ and rate constants $\kappa = (\kappa_{ij})$ has mass-action ODEs

$$\frac{dx}{dt} = \sum_{y_i \to y_j \in \mathcal{R}} \kappa_{ij}\, x^{y_i} (y_j - y_i) =: \big(f_1(x), \dots, f_n(x)\big).$$

The **steady-state ideal** is $I_N = \langle f_1, \dots, f_n \rangle \subseteq \mathbb{Q}[\kappa; x]$; its elements are **steady-state invariants**. For observable species $x_{j_1}, \dots, x_{j_l}$ the invariants involving only them form the elimination ideal $I_N^{\mathrm{elim}} = I_N \cap \mathbb{Q}[\kappa; x_{j_1}, \dots, x_{j_l}]$.

Let $N = N_1 \cup N_2$ be obtained by **gluing** $N_1$ and $N_2$ over complexes (a nonzero complex in common, no common reaction) or over reactions (at least one common reaction). Write $\kappa(i), x(i)$ for the rate constants and species of $N_i$, and let $\varphi_i : \mathbb{Q}[\kappa; x] \to \mathbb{Q}[\kappa(i); x(i)]$ be the ring homomorphism fixing $\kappa(i)$ and $x(i)$ and sending every other rate constant and species to $0$.

**Theorem (Gross–Harrington–Meshkat–Shiu).** For $i = 1, 2$:
1. $\varphi_i(I_N) = I_{N_i}$;
2. $\varphi_i\big(I_N \cap \mathbb{Q}[\kappa; x_{j_1}, \dots, x_{j_l}]\big) \subseteq I_{N_i} \cap \mathbb{Q}[\kappa(i); x_{j_1}, \dots, x_{j_l}]$, i.e. $\varphi_i(I_N^{\mathrm{elim}}) \subseteq I_{N_i}^{\mathrm{elim}}$: every invariant of the glued network specializes to an invariant of each piece.

The containment in 2 can be strict. For $N_1 = \{X_1 \xrightarrow{\kappa_1} X_2\}$, $N_2 = \{X_2 \xrightarrow{\kappa_2} X_1\}$ glued over complexes into $N = \{X_1 \rightleftharpoons X_2\}$, one has $I_N = \langle -\kappa_1 x_1 + \kappa_2 x_2 \rangle$, $I_{N_2} = \langle \kappa_2 x_2 \rangle$, and eliminating $x_1$ gives $I_N^{\mathrm{elim}(x_1)} = \langle 0 \rangle$ while $I_{N_2}^{\mathrm{elim}(x_1)} = \langle \kappa_2 x_2 \rangle$; so $\varphi_2(I_N^{\mathrm{elim}}) = \langle 0 \rangle \subsetneq I_{N_2}^{\mathrm{elim}}$. Hence, after elimination, the observable invariants of a piece cannot in general be recovered by specializing the observable invariants of the whole network. The full steady-state ideals, by contrast, are recovered by specialization, by item 1; the strict containment concerns only elimination ideals.

## Expansion

Mass-action vector fields are sums over reactions. When $\mathcal{R}_1 \cap \mathcal{R}_2 = \varnothing$ the system polynomials of $N$ are $h_j = f_j + g_j$ (extending each $f_j, g_j$ by zero to the missing species). When reactions are shared, $h_j = f_j + \tilde g_j$, where $\tilde g_j$ comes from the reactions of $N_2$ not in $N_1$. In both cases $\varphi_1$ kills every monomial of $\tilde g_j$ (each carries a rate constant outside $\kappa(1)$) and fixes $f_j$, so $\varphi_1(h_j) = f_j$. Since $\varphi_1$ is a surjective ring homomorphism, $\varphi_1(I_N) = \langle \varphi_1(h_j) \rangle = I_{N_1}$. The containment in 2 follows because $\varphi_i$ maps polynomials in the observable variables to polynomials in the observable variables. Strictness arises because $\varphi_i$ commutes with taking ideals but not with intersecting with a subring.

## Sources

- E. Gross, H. Harrington, N. Meshkat and A. Shiu, "Joining and decomposing reaction networks", Journal of Mathematical Biology (2020), Sections 2.3 and 4 (Definition 2.3, Lemma 2.8, Definition 4.1, Lemma 4.3, Proposition 4.4, Example 4.5), <https://doi.org/10.1007/s00285-020-01477-y>.
