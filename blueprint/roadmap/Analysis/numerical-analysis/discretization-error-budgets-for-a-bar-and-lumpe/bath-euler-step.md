# Explicit Euler step for bath cooling

For real $C$, $G$, $T_{\mathrm{amb}}$, a time step $\Delta t$ and a temperature $T$, one explicit Euler step of $C\,T' = Q(T)$ with $Q(T) = -G(T - T_{\mathrm{amb}})$ is

$$T \mapsto T + \frac{\Delta t\, Q(T)}{C}.$$

Real division by zero is $0$, so at $C = 0$ the step is the identity $T \mapsto T$. For $C \neq 0$ it is the explicit Euler step of $C\,T' = Q(T)$; at $C = 0$ it is not a step of that equation, which then reads $0 = Q(T)$.
