# Fleming–Viot limit of spatial populations with fast density regulation

Individuals of $q$ types $Q = \{1,\dots,q\}$ live in a compact metric space $E$ (geographic space, or a trait space). With scaling parameter $N$, each individual has mass $1/N$, the population is $\mu^N = (\mu^N_1,\dots,\mu^N_q)$ with $\mu^N_i$ the mass measure of type $i$, and $h = H(\mu) = (\mu_1(E),\dots,\mu_q(E))$ is the **density vector**. In the basic model:

- each type-$i$ individual migrates by an independent Markov process with generator $B_i$ (slow);
- at density $h$, each type-$i$ individual gives birth to a type-$j$ individual at the same location at rate $N\beta_{ij}(h)$ and dies at rate $N\rho_i(h)$ (fast).

Let $A(h)$ have entries $A_{ij}(h) = \beta_{ji}(h)$ for $i \neq j$ and $A_{ii}(h) = \beta_{ii}(h) - \rho_i(h)$, and $\theta(h) = A(h)h$. Assume: there is $h_{\mathrm{eq}} \neq 0$ with $\theta(h_{\mathrm{eq}}) = 0$; the Jacobian of $\theta$ at $h_{\mathrm{eq}}$ is stable; $A(h_{\mathrm{eq}})$ is irreducible; $\beta_{ij}, \rho_i$ are analytic near $h_{\mathrm{eq}}$. Let $U_{\mathrm{eq}}$ be the basin of $h_{\mathrm{eq}}$ for $\dot h = \theta(h)$, and let $v_{\mathrm{eq}} > 0$ be the left null vector of $A(h_{\mathrm{eq}})$ normalized by $\langle v_{\mathrm{eq}}, h_{\mathrm{eq}}\rangle = 1$ (then $h_{\mathrm{eq}} > 0$).

**Proposition (density pinning).** If $h^N(0)$ stays in a compact subset of $U_{\mathrm{eq}}$ and $t_N \to 0$ with $N t_N \to \infty$, then $\sup_{t\le T}\|h^N(t + t_N) - h_{\mathrm{eq}}\|_1 \Rightarrow 0$, and the $q$ type-components become spatially inseparable.

**Theorem.** If $\mu^N(0) \Rightarrow \mu(0)$ with $H(\mu(0)) \in U_{\mathrm{eq}}$ a.s., then $\hat\mu^N(t) = \mu^N(t + t_N)$ converges in distribution to $h_{\mathrm{eq}}\,\nu$, where $\nu$ is the neutral Fleming–Viot process on $\mathcal P(E)$ with generator, for $F(\nu) = \prod_{l=1}^m \langle f_l, \nu\rangle$,

$$\mathbf A_0 F(\nu) = \sum_{l=1}^m \langle B_{\mathrm{avg}} f_l, \nu\rangle \prod_{j\neq l}\langle f_j,\nu\rangle + \gamma \sum_{l \neq k}\big(\langle f_l f_k, \nu\rangle - \langle f_l,\nu\rangle\langle f_k,\nu\rangle\big)\prod_{j \neq l,k}\langle f_j,\nu\rangle,$$

with averaged mutation operator and resampling rate

$$B_{\mathrm{avg}} = \sum_{i} v_{\mathrm{eq},i} h_{\mathrm{eq},i} B_i, \qquad \gamma = \sum_i v_{\mathrm{eq},i}^2\, h_{\mathrm{eq},i}\, \rho_i(h_{\mathrm{eq}}).$$

Adding order-one position-dependent birth and death rates produces a selection term with averaged fitness $b^s_{\mathrm{avg}} - d^s_{\mathrm{avg}}$, and rare or small offspring dispersal or immigration produces additional averaged mutation terms.

## Expansion

Fast birth and death pin the density to $h_{\mathrm{eq}}$ (a Katzenberger-type stochastic averaging onto the stable fixed point). Once the total mass is pinned, every birth must be compensated by a death at a location drawn from the current empirical measure, which is exactly the resampling mechanism of a Fleming–Viot process; migration, being slow and location-only, becomes mutation. To pass to the limit one studies the combination $\nu^N = \sum_i \Lambda_i(h^N)\mu^N_i$, where $\Lambda$ solves a system of first-order PDEs along the density flow chosen so that the fast terms cancel; $\Lambda(h_{\mathrm{eq}}) = v_{\mathrm{eq}}$, which explains the weights $v_{\mathrm{eq},i}h_{\mathrm{eq},i}$ in the averaged operators. The PDE solution is built analytically near $h_{\mathrm{eq}}$ and extended to the basin.

## Sources

- Ankit Gupta, "The Fleming-Viot limit of an interacting spatial population with fast density regulation", *Electronic Journal of Probability* 17 (2012), <https://doi.org/10.1214/EJP.v17-1964>; preprint arXiv:1204.2909, <https://doi.org/10.48550/arXiv.1204.2909>. Numbering of the arXiv version: Section 2 (density regulation mechanism, Assumption on $\theta$, basic and extended models, Propositions 2.4 and 2.5, generators $\mathbf A_0$–$\mathbf A_3$, resampling rate, Theorem 2.6), Section 4 (Propositions 4.6–4.8), Appendix (Lemma A.1).
