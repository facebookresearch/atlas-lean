# Constant step sizes recover fixed-step online gradient descent

Let $E$ be a real inner product space, $\mathrm{proj} : E \to E$, $g : \mathbb{N} \to E \to E$, $\eta \in \mathbb{R}$ and $x_0 \in E$. The varying-step projected online gradient descent iterates with the constant schedule $\eta_t = \eta$ for all $t$ are exactly the fixed-step iterates $x_0$, $x_{t+1} = \mathrm{proj}(x_t - \eta\, g_t(x_t))$, at every round.
