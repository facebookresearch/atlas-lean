# Damage lifetime

For a damage path $d : \Omega \to \mathbb{R}_{\ge 0} \to \mathbb{R}$, a threshold $D : \Omega \to \mathbb{R}$ and a scenario $\omega$, the damage lifetime $\tau(\omega) \in [0, \infty]$ is the hitting time of $t \mapsto d(\omega, t) - D(\omega)$ into $[0, \infty)$ from time $0$:

$$\tau(\omega) = \begin{cases} \inf\{t \in \mathbb{R}_{\ge 0} : d(\omega, t) \ge D(\omega)\} & \text{if some } t \ge 0 \text{ has } d(\omega, t) \ge D(\omega), \\ \infty & \text{otherwise.} \end{cases}$$
