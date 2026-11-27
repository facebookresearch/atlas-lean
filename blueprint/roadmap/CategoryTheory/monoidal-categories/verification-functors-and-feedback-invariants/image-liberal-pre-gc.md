# Direct image is left adjoint to the liberal precondition

In the category of sets and relations with the disjoint union as tensor, a relation $f : X \to Y$ acts on assertions $P \subseteq X$ by direct image $f[P]$, and its liberal precondition sends $Q \subseteq Y$ to $\operatorname{wlp}_f(Q) = \{x : \text{every } y \text{ related to } x \text{ by } f \text{ lies in } Q\}$. For a relation $f : X \to Y$, $P \subseteq X$ and $Q \subseteq Y$,

$$f[P] \subseteq Q \iff P \subseteq \operatorname{wlp}_f(Q),$$

so direct image and liberal precondition form a Galois connection. Since the powerset verification functor relates $P$ to $Q$ exactly when $f[P] \subseteq Q$, this says that $(P, Q)$ lies in the verification relation of $f$ if and only if $P \subseteq \operatorname{wlp}_f(Q)$.
