# Explicit Euler step for bath cooling

For real $C$, $G$, $T_{\mathrm{amb}}$, a time step $\Delta t$ and a temperature $T$, one explicit Euler step of $C\,T' = Q(T)$ with $Q(T) = -G(T - T_{\mathrm{amb}})$ is

$$T \mapsto T + \frac{\Delta t\, Q(T)}{C}.$$
