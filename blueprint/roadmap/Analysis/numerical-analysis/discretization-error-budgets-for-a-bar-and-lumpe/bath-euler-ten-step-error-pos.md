# Ten-step Euler error for bath cooling is nonzero

Let $C > 0$, $G > 0$, real $T_{\mathrm{amb}}$ and $\Delta$, and put $\tau = C/G$ and $Q(T) = -G(T - T_{\mathrm{amb}})$. Assume $\Delta \ne 0$. Let $(X_j)_{j \in \mathbb{N}}$ be a real sequence with $X_0 = T_{\mathrm{amb}} + \Delta$ and $X_{j+1} = X_j + (\tau/10)\, Q(X_j)/C$ for every $j$ (explicit Euler steps of size $\tau/10$). With $T(t) = T_{\mathrm{amb}} + \Delta\, e^{-t/\tau}$,

$$0 < |X_{10} - T(\tau)|.$$
