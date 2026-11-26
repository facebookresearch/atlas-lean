# Varying steps are unit steps with scaled gradients

Let $E$ be a real inner product space, $\mathrm{proj} : E \to E$, gradients $g_t : E \to E$, step sizes $\eta_t$ and $x_0 \in E$. The projected online gradient iterates with step sizes $\eta_t$, $x_{t+1} = \mathrm{proj}(x_t - \eta_t g_t(x_t))$, coincide (as sequences) with the fixed-step iterates at step $1$ for the scaled gradients $\eta_t g_t$.
