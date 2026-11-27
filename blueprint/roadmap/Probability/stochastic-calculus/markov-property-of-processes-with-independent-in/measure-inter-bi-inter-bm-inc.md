# Past events factor against grid increments

Let $\mu$ be a probability measure and let
$(B_t)_{t \ge 0}$ be a real process adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ such that
$B_t - B_s$ is independent of $\mathcal{F}_s$ under $\mu$ whenever $s \le t$. Let
$s \in \mathbb{R}_{\ge 0}$ and let $S \subseteq \mathbb{R}_{\ge 0}$ be finite. For $t \in S$ let
$\Delta_t = B_{s+t} - B_{s+t^-}$, where $t^-$ is the largest element of $S$ strictly below $t$, or
$0$ if there is none. Then for every family $(C_t)_{t \ge 0}$ of Borel subsets of $\mathbb{R}$ and
every $A \in \mathcal{F}_s$,

$$\mu\Big(A \cap \bigcap_{t \in S} \{\Delta_t \in C_t\}\Big)
= \mu(A)\,\mu\Big(\bigcap_{t \in S} \{\Delta_t \in C_t\}\Big).$$

The proof is induction on $S$ by its maximum element $a$: the increment $\Delta_a$ is independent
of $\mathcal{F}_{s + a^-}$, which contains both $A$ and the earlier increments.
