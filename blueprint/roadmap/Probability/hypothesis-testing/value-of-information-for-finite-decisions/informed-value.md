# Informed Value

Let $\Omega$ (states) and $E$ (evidence outcomes) be finite sets, $w : \Omega \times E \to \mathbb{R}$ a joint weight, $U(a, \omega)$ the utility of action $a$ in state $\omega$, and $A$ a finite nonempty set of actions. The unnormalized expected utility of acting after seeing the evidence is

$$V_{\mathrm{inf}} = \sum_{e \in E} \max_{a \in A} \sum_{\omega \in \Omega} w(\omega, e)\, U(a, \omega),$$

choosing for each evidence outcome the best action under the joint weights for that outcome. Nonemptiness of $A$ makes each maximum exist.
