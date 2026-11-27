# Positive additivity of reachability and irreducible state spaces of stochastic reaction networks

**Setting.** A stochastic reaction network on $d$ species with $K$ reactions is a continuous-time Markov chain on $\mathbb N_0^d$: reaction $k$ consumes $\nu_k$ and produces $\nu'_k$ molecules and fires at rate $\lambda_k(x)$. Assume the **mass-action-type** condition: $\lambda_k(x) > 0$ if and only if $x_i \ge \nu_{ik}$ for all $i$. Conservation relations $\Gamma x = c$ restrict the chain to $\mathcal E_0 = \{x \in \mathbb N_0^d : \Gamma x = c\}$. A set $\mathcal E \subset \mathcal E_0$ is an **irreducible state space** if it is closed under the dynamics and any two of its states communicate.

**Proposition (positive additivity).** The reachability relation $x \to y$ is positively additive on $\mathcal E_0$: if $x \to y$ and $x + z \in \mathcal E_0$ for some $z \in \mathbb N_0^d$, then $y + z \in \mathcal E_0$ and $x + z \to y + z$.

**Proposition (decomposition).** After a permutation of species, every species is either *bounded* (its copy number is bounded on $\mathcal E_0$), *free* or *restricted* (unbounded, with restricted species affine functions $\phi$ of free ones). If no conservation relation couples bounded with free/restricted species, then

$$\mathcal E_0 \cong \mathcal E_b \times \Phi,$$

where $\mathcal E_b$ is the finite bounded-species state set and $\Phi$ is the graph of the affine map $\phi$; irreducible state spaces of the network correspond to those of a reduced network on bounded and free species, $F \times G \leftrightarrow F \times \Phi_G$.

**Theorem (identification).** Organize the bounded-species communication classes and the sets of free species that can be produced from them into a finite tree (the birth-cascade tree). If a minimal leaf $(C, A)$ is *death-exhaustive* and every free species that must be removed is *singularly degradable* (its negative unit vector lies in the $\mathbb N_0$-span of the stoichiometry vectors of available reactions), then

$$C \times \mathbb N_0^{|A|} \times \{\mathbf 0\}$$

is an irreducible state space, and under a further degradability condition it is the only one meeting $C \times \mathbb N_0^{d_f}$. If all leaves are minimal and satisfy these conditions, these sets are, up to relabeling, all the irreducible state spaces.

## Proof sketch

Positive additivity holds because a reaction path enabled from $x$ remains enabled from $x + z$ under the mass-action-type condition: extra molecules never block a reaction. It allows communication classes to be computed on a finite "core" and then extended by translation in the unbounded directions. The procedure is purely linear-algebraic and combinatorial, and its output (closed irreducible classes) is what is needed before speaking of a unique stationary distribution, ergodicity or finite-state-projection truncations.

## Sources

- Ankit Gupta and Mustafa Khammash, "Computational Identification of Irreducible State-Spaces for Stochastic Reaction Networks", *SIAM Journal on Applied Dynamical Systems* 17 (2018), 1213–1266, <https://doi.org/10.1137/17m1134299>. Preprint version: arXiv:1505.06594 (2015), Assumption 3.1, Propositions 3.2–3.3 (Section 3), Proposition 4.2 (Section 4), Propositions 5.2–5.3 and Theorem 5.4 (Section 5), <https://doi.org/10.48550/arXiv.1505.06594>.
