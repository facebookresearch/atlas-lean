# The pair-section identity for measurable sets

Let $\mu$ be a probability measure and
let $(B_t)_{t \ge 0}$ be a real process adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ such
that $B_t - B_s$ is independent of $\mathcal{F}_s$ under $\mu$ whenever $s \le t$. Fix
$s \in \mathbb{R}_{\ge 0}$, let $W^s$ be the centered shifted path $t \mapsto B_{s+t} - B_s$ and
let $\nu_s$ be its law under $\mu$. Then for every set
$T \subseteq \mathbb{R} \times (\mathbb{R}_{\ge 0} \to \mathbb{R})$ that is measurable for the
product σ-algebra and every $A \in \mathcal{F}_s$,

$$\mu\big(A \cap \{(B_s, W^s) \in T\}\big)
= \int_A \nu_s\big(\{f : (B_s(\omega), f) \in T\}\big)\,d\mu(\omega).$$

The proof is Dynkin's theorem over cylinder rectangles.
