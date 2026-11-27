# Euler step of three time constants is unstable for bath cooling

Let $C > 0$, $G > 0$, real $T_{\mathrm{amb}}$ and $\Delta$, and put $\tau = C/G$ and $Q(T) = -G(T - T_{\mathrm{amb}})$. Let $(X_j)$ be a real sequence with $X_0 = T_{\mathrm{amb}} + \Delta$ and $X_{j+1} = X_j + 3\tau\, Q(X_j)/C$. Then

- $|T(t) - T_{\mathrm{amb}}| \le |\Delta|$ for every $t \ge 0$, where $T(t) = T_{\mathrm{amb}} + \Delta\, e^{-t/\tau}$;
- $X_j = T_{\mathrm{amb}} + \Delta(-2)^j$ and $|X_j - T_{\mathrm{amb}}| = 2^j |\Delta|$ for every $j$.
