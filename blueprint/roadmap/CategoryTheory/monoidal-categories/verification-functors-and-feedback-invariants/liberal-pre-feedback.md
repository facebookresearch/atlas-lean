# Liberal precondition of finite-path feedback

In the category of sets and relations with the disjoint union as tensor, a relation $f : X \to Y$ acts on assertions $P \subseteq X$ by direct image $f[P]$, and its liberal precondition sends $Q \subseteq Y$ to $\operatorname{wlp}_f(Q) = \{x : \text{every } y \text{ related to } x \text{ by } f \text{ lies in } Q\}$. For $f : X \sqcup U \to Y \sqcup U$ and $Q \subseteq Y$, a state $s \in X \sqcup U$ is one-step safe for a hidden assertion $I \subseteq U$ when every successor of $s$ under $f$ is either $\mathrm{inl}(y)$ with $y \in Q$ or $\mathrm{inr}(u)$ with $u \in I$, that is, when $s \in \operatorname{wlp}_f(Q \sqcup I)$; no successor is required. Let $I_Q$ be the greatest fixed point of the [one-step safety map](feedback-step.md) $I \mapsto \{u : \mathrm{inr}(u) \text{ is one-step safe for } I\}$. Then the liberal precondition of the [feedback](../relations-with-disjoint-union-tensor/feedback.md) of $f$ is

$$\operatorname{wlp}_{\operatorname{feedback}(f)}(Q) = \{x : \mathrm{inl}(x) \text{ is one-step safe for } I_Q\}.$$

Every next output of $\mathrm{inl}(x)$ must be visible in $Q$ or hidden in $I_Q$. Even when $U$ is empty, a direct edge from $\mathrm{inl}(x)$ to $\mathrm{inl}(y)$ contributes to the feedback and must satisfy $y \in Q$.
