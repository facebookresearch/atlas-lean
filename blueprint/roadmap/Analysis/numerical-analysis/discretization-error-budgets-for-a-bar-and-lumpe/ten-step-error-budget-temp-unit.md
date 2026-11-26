# Ten-step error budget scales with the temperature unit

Let $k > 0$ and real $c$, $C$, $G$, $T_{\mathrm{amb}}$, $\Delta$ and $Y : \mathbb{N} \to \mathbb{R}$. Change the temperature unit by $T \mapsto kT + c$: replace $T_{\mathrm{amb}}$ by $kT_{\mathrm{amb}} + c$, $Y_i$ by $kY_i + c$, $\Delta$ by $k\Delta$, and $C$, $G$ by $C/k$, $G/k$. Then

- every Euler residual $\eta_j$ (step size $\tau/10$, $\tau = C/G$) is multiplied by $k$;
- the ten-step error budget $\left(\tfrac{9}{10}\right)^{10} |Y_0 - (T_{\mathrm{amb}} + \Delta)| + \sum_{j=0}^{9} \left(\tfrac{9}{10}\right)^{9-j} |\eta_j| + |\Delta|/10$ is multiplied by $k$.

Real division by zero is $0$: $\tau = C/G$ is $0$ when $G = 0$, and $Q(T)/C$ is $0$ when $C = 0$, so then the Euler step is the identity.
