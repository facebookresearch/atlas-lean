# Fold-change detection in a two-cluster MWC chemotaxis model

**Model.** The chemotaxis pathway of *Rhodobacter sphaeroides* has two receptor clusters: transmembrane receptors that sense the external ligand $L(t)$ and cytoplasmic receptors that sense an internalized signal $\tilde L(t)$. Let $a, \tilde a \in (0,1)$ be the activities of the two clusters and $m, \tilde m$ their methylation levels. Under a Monod–Wyman–Changeux (two-state allosteric) model,

$$a = \frac{1}{1 + \exp\big(-g_m(m) - g_L(L)\big)}, \qquad g_m(m) = \alpha(m_0 - m), \qquad g_L(L) = \ln\Big(1 + \frac{L}{K_I}\Big) - \ln\Big(1 + \frac{L}{K_A}\Big),$$

with $K_A \gg K_I > 0$ (ligand binds inactive receptors more strongly). The formula for $\tilde a$ is the same, with $\tilde\alpha, \tilde m_0, \tilde K_I, \tilde K_A$ and $\tilde L$. In the intermediate range $K_I \ll L \ll K_A$ (and likewise for $\tilde L$) this becomes

$$a \approx G(m, L) = \frac{1}{1 + e^{\alpha(m_0 - m)}\,L/K_I}, \qquad \tilde a \approx \tilde G(\tilde m, \tilde L) = \frac{1}{1 + e^{\tilde\alpha(\tilde m_0 - \tilde m)}\,\tilde L/\tilde K_I}.$$

Methylation and the phosphorylation network $\mathbf x$ (the CheA, CheB, CheY proteins) evolve as

$$\dot m = F\big(a, w(\mathbf x)\big), \qquad \dot{\tilde m} = \tilde F\big(\tilde a, \tilde w(\mathbf x)\big), \qquad \dot{\mathbf x} = H(\mathbf x, a, \tilde a).$$

The functions $F$, $\tilde F$, $H$, $w$, $\tilde w$ are arbitrary, but $m, \tilde m$ enter the right-hand sides only through $a, \tilde a$.

**Assumption 1 (linear internalization).** The internal signal is a linear time-invariant filter of a power of the external ligand:

$$\dot\xi = A\xi + B(u)L^{\nu}, \qquad \tilde L = C\xi + D(u)L^{\nu},$$

with $\xi \in \mathbb R^n$, $A \in \mathbb R^{n\times n}$, $C \in \mathbb R^{1\times n}$, $\nu \in \mathbb R$, and $u = u(\mathbf x, a)$.

**Assumption 2.** For each constant $L$ the combined system has a unique steady state.

**Definition (FCD).** The system shows *fold-change detection* if, starting from the steady state for $L(0)$, the activity trajectories $a(t), \tilde a(t)$ are unchanged when the input $L(t)$ is replaced by $pL(t)$ for any $p > 0$.

**Theorem.** Under Assumptions 1 and 2 and the intermediate-range approximation, the two-cluster system with steady-state initial conditions shows FCD in $a$ and $\tilde a$, and therefore in every downstream phosphorylated protein and in the flagellar response.

## Proof sketch

The proof exhibits an equivariance. If $(m_1, \tilde m_1, \mathbf x_1, \xi_1)(t)$ solves the system for input $L_1(t)$, then

$$\big(m_1 + \tfrac{1}{\alpha}\log p,\ \tilde m_1 + \tfrac{\nu}{\tilde\alpha}\log p,\ \mathbf x_1,\ p^{\nu}\xi_1\big)(t)$$

solves it for input $pL_1(t)$. The reason is that $G(m + \alpha^{-1}\log p,\ pL) = G(m, L)$, the linear filter gives $\tilde L_2 = p^{\nu}\tilde L_1$, and $\tilde G(\tilde m + \tilde\alpha^{-1}\nu\log p,\ p^{\nu}\tilde L) = \tilde G(\tilde m, \tilde L)$. So the activities, and hence every right-hand side, are unchanged. By Assumption 2 the steady state for $pL_1(0)$ is the shifted one, so uniqueness of solutions gives $a_2 = a_1$ and $\tilde a_2 = \tilde a_1$. FCD is a dynamic phenotype that a model can fail to have. The paper uses it to tell apart two candidate *R. sphaeroides* pathway topologies: an FCD experiment with a scaled stimulus would invalidate the model whose cytoplasmic cluster does not sense a linearly filtered ligand signal.

## Sources

- Abdullah Hamadeh, Brian Ingalls and Eduardo Sontag, "Transient dynamic phenotypes as criteria for model discrimination: fold-change detection in Rhodobacter sphaeroides chemotaxis", *Journal of The Royal Society Interface* 10 (2013), 20120935, <https://doi.org/10.1098/rsif.2012.0935>. Preprint version: arXiv:1204.1941 (2012), Section 1.1 (Assumption 1), Section 1.2 (MWC receptor model and the intermediate-range approximation) and Section 2 (Definition 1, Assumption 2, Theorem 1 and its proof), <https://doi.org/10.48550/arXiv.1204.1941>.
