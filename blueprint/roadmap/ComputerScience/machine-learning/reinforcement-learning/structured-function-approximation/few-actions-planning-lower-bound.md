# Planning lower bound with few actions under linear realizability

Exponential query cost under linear realizability does not need exponentially many actions. With $A \ge d^{1/4} \wedge H^{1/2}$ actions and deterministic transitions, planning to accuracy $0.01$ needs $2^{\Omega(d^{1/4} \wedge H^{1/2})}$ queries, whether $v^\star$, $q^\star$, or both on reachable states are linear, even with global access.

**Classes.** For $B \ge 0$ and positive integers $d, H, A$, consider featurized fixed-horizon MDPs with finite state space, actions $[A]$, horizon $H$ (stages encoded in the states, with a final absorbing zero-reward state), random rewards in $[0,1]$ and total expected reward as the objective:

- $\mathcal{M}^{v^\star}_{B,d,H,A}$: a feature map $\varphi : \mathcal{S} \to \mathbb{R}^d$ with $\sup_s \lVert\varphi(s)\rVert_2 \le 1$ and some $\lVert\theta^\star\rVert_2 \le B$ with $v^\star(s) = \varphi(s)^{\mathsf T}\theta^\star$ for all $s$;
- $\mathcal{M}^{q^\star}_{B,d,H,A}$: $\varphi : \mathcal{S}\times[A] \to \mathbb{R}^d$ with $\lVert\varphi\rVert_2 \le 1$ and $q^\star(s,a) = \varphi(s,a)^{\mathsf T}\theta^\star$ for all $(s,a)$, $\lVert\theta^\star\rVert_2 \le B$;
- $\mathcal{M}^{v^\star/q^\star\,\mathrm{reach}}_{B,d,H,A}$: two feature maps of norm at most $1$ and one $\theta^\star$ with $\lVert\theta^\star\rVert_2 \le B$ realizing both $v^\star$ and $q^\star$ on every state reachable from the initial states.

$\mathcal{M}^{\mathrm{Pdet}}$ denotes the featurized MDPs with deterministic transitions (rewards may be random). A planner, called with the current state, queries a simulator and returns an action; it is $\delta$-sound for a class if, from every start state of every member, its total expected reward is within $\delta$ of optimal. Under *global access* the planner knows all states and features in advance and may query any state. Its query cost is the worst-case expected number of queries in a call, and $C^\star_{\mathrm{GA}}(\mathcal{M},\delta)$ is the minimax query cost over $\delta$-sound planners.

**Theorem.** For $B \ge 315$, $d \ge 31$, $H \ge 81$, $A \ge d^{1/4} \wedge H^{1/2}$, every $0 < \delta \le 0.01$, and $\mathcal{M}$ any of the three classes above,

$$
C^\star_{\mathrm{GA}}\big(\mathcal{M} \cap \mathcal{M}^{\mathrm{Pdet}}, \delta\big) = 2^{\Omega(d^{1/4} \wedge H^{1/2})}.
$$

Since global access is easier than local access, the same lower bound holds for planners with local access only.

**Scope.** The bound is information-theoretic and holds against planners with unbounded computation. For a fixed number of actions it is complemented by the source's local-access upper bound $\mathrm{poly}((dH/\delta)^A, B)$ for $\mathcal{M}^{v^\star}$, for $\mathcal{M}^{v^\star/q^\star\,\mathrm{reach}}$, and for $\mathcal{M}^{q^\star} \cap \mathcal{M}^{\mathrm{Pdet}}$. The source contrasts this with a polynomial upper bound of Du et al. (2021) when $v^\star$ and $q^\star$ are both realizable at all states, not just reachable ones.

## Depends on

- [Probability measure](../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

An abstract guessing game is built first. The agent picks corners of a $p$-dimensional hypercube in sequence, $p \approx H^{1/2} \wedge d^{1/4}$, for up to $K \approx H/p$ picks. Each pick must differ substantially from the previous one, and the achievable reward shrinks by a penalty factor after each pick. A pick close to the secret corner $w^\star$ ends the game with the best achievable reward; otherwise the final reward is Bernoulli with mean $\exp(-\Omega(K))$. Finding $w^\star$ is a needle-in-a-haystack problem, so any sound player needs $2^{\Omega(p \wedge K)}$ queries (Theorem 4.1). The game is embedded in a deterministic featurized MDP whose number of actions is set by the source's Eq. (21), with $A \ge p$; using fewer actions than allowed is no restriction, since actions can be duplicated. The optimal policy is greedy and its value is a polynomial of degree $4$ in $w^\star$, so features of dimension $d \approx p^4$ realize $v^\star$, $q^\star$, or both on reachable states, with $\lVert\theta^\star\rVert_2 \le B$ (Lemmas 4.14–4.16). Each MDP query is simulated with at most one game query (Lemma 4.6). A $0.01$-sound planner with query cost $\bar N$ therefore yields a sound game player with cost $8p\bar N + 8p$, so $\bar N = 2^{\Omega(H^{1/2} \wedge d^{1/4})}$.

The published Theorem 1.1 asks for $\delta, B, d, H$ "sufficiently large". Read literally, the quantifier on $\delta$ is inverted: for $\delta \ge H$ every planner is sound with zero queries, and the source's own Theorem 2.1 phrases the companion result for $\delta > 0$ sufficiently small. The proof (Section 4.8) argues for $0.01$-sound planners with $B \ge 315$, $d \ge 31$ and $H \ge 81$, so it covers every $0 < \delta \le 0.01$, and that is the form stated here.

A complete expansion adds pages for the abstract-game lower bound (Theorem 4.1), the simulation of the MDP by the game with one game query per MDP query (Lemma 4.6), and the realizability lemmas for the three classes (Lemmas 4.14–4.16).

## Sources

- G. Weisz, Cs. Szepesvári and A. György, "TensorPlan and the Few Actions Lower Bound for Planning in MDPs under Linear Realizability of Optimal Value Functions", Algorithmic Learning Theory (ALT 2022), PMLR 167:1097–1137. Numbers from arXiv:2110.02195v2: Section 1 (classes, soundness, query cost), Theorem 1.1, Theorem 1.2, Eq. (1), Theorem 2.1, Assumption 3.1, Theorem 4.1, Lemmas 4.6 and 4.14–4.16, Section 4.8 (proof of Theorem 1.1). <https://arxiv.org/abs/2110.02195v2>
