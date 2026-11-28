# Linear-programming certificates of ergodicity for stochastic reaction networks

**Setting.** A reaction network with $d$ species and reactions $k \in \mathcal{K}$ ($K$ of them), reactant and product vectors $\nu_k, \nu'_k \in \mathbb{N}_0^d$, stoichiometry matrix $M = [\nu'_k - \nu_k]_{k}$ and mass-action propensities with rate constants $\theta_k > 0$, is modelled as a continuous-time Markov chain on a state space $\mathcal{S} \subset \mathbb{N}_0^d$ (the chemical master equation). The dynamics is **ergodic** if there is a probability distribution $\pi$ with

$$\lim_{t\to\infty}\sup_{A \subset \mathcal{S}}|p_x(t,A) - \pi(A)| = 0 \qquad \text{for every } x \in \mathcal{S},$$

which identifies the long-term behaviour of a cell population with the stationary law of a single cell.

**Theorem (irreducibility, no conservation laws).** Suppose $\mathrm{Rank}(M) = d$, the integer column span of $M$ is $\mathbb{Z}^d$, and the linear feasibility problem

$$\mathcal{F}_1 = \{v \in \mathbb{R}^K : Mv = 0,\ v \ge \mathbf{1}\}$$

has a solution; assume also that the network and its reversed network are exhaustive (from abundant reactants, every species can be emptied, level by level). Then $\mathcal{S} = \mathbb{N}_0^d$ is irreducible. An analogous statement with a reduced stoichiometry matrix $\bar M$ for the $d_u$ unconserved species and an LFP $\mathcal{F}_2$ gives irreducibility of $\mathbb{N}_0^{d_u} \times \mathcal{E}_c$, where $\mathcal{E}_c$ is the finite set of states of the conserved species.

**Theorem (ergodicity).** Suppose every reaction has at most two reactant molecules, $\mathcal{S} = \mathbb{N}_0^{d_u} \times \mathcal{E}_c$ is irreducible, and there is $w \in \mathbb{R}^d$ with strictly positive first $d_u$ components such that

$$A w < 0 \qquad \text{and} \qquad w^{\top}M_q = 0,$$

where $A = \sum_{k \in \mathcal{K}_{\mathrm{unr}}}\theta_k\,a_k(\nu'_k - \nu_k)^{\top}$ sums over unary reactions $S_i \to \star$ of unconserved species ($a_k$ the $i$-th unit vector in $\mathbb{R}^{d_u}$) and $M_q$ has as columns the net changes $\nu'_k - \nu_k$ of the binary reactions. Such a $w$ exists iff a linear feasibility problem $\mathcal{F}_3$ has a solution. Then the reaction dynamics is ergodic.

## Proof sketch

The linear function $V(x) = \langle w, x\rangle + c$ is a Foster–Lyapunov function: binary reactions, whose propensities are quadratic, do not change $V$ because $w^{\top}M_q = 0$; unary reactions contribute the drift $(Aw)\cdot x_u$, which is negative and linear in the unconserved counts; constitutive reactions add a constant. This gives the negative-drift condition $\mathcal{L}V \le -c_1 V + c_2$, and with irreducibility the Meyn–Tweedie theorem yields exponential ergodicity. Every condition is a linear program in the network's stoichiometry, so the test scales to large networks (for example a 9-species, 16-reaction genetic oscillator).

## Sources

- Ankit Gupta and Mustafa Khammash, "Determining the long-term behavior of cell populations: A new procedure for detecting ergodicity in large stochastic reaction networks", *IFAC Proceedings Volumes* 47 (2014), 1711–1716, <https://doi.org/10.3182/20140824-6-za-1003.00291>. Preprint version: arXiv:1312.2879 (2013), Theorems 3.2, 3.4 and 3.6, Lemma 3.5, and the genetic-oscillator example, <https://doi.org/10.48550/arXiv.1312.2879>.
