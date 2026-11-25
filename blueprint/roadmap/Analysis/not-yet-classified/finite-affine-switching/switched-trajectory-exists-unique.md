# Existence and uniqueness of a switched affine trajectory

Let $E$ be a real Banach space, $A : E \to E$ a bounded linear operator, $\tau_0 < \tau_1 < \dots < \tau_n$ switch times, $b : \mathbb{R} \to E$ a forcing, and $x_0 \in E$. For each piece $k < n$ let $g_k : \mathbb{R} \to E$ be continuous on $[\tau_k, \tau_{k+1}]$ with $b = g_k$ on $(\tau_k, \tau_{k+1})$. Call $y : \mathbb{R} \to E$ a switched trajectory if $y(\tau_0) = x_0$, $y$ is continuous on $[\tau_0, \tau_n]$, and $y'(t) = A y(t) + b(t)$ at every $t \in (\tau_k, \tau_{k+1})$ for every $k$. Then there is a switched trajectory $x$ such that:

- for every $k$ and $t \in [\tau_k, \tau_{k+1}]$, $x(t) = e^{(t - \tau_k)A} x(\tau_k) + \int_{\tau_k}^{t} e^{(t - s)A} b(s)\,ds$;
- for every $k$ and $t \in [\tau_k, \tau_{k+1}]$, $x$ has derivative $A x(t) + g_k(t)$ at $t$ within $[\tau_k, \tau_{k+1}]$;
- $s \mapsto A x(s) + b(s)$ is interval integrable on $[\tau_0, \tau_n]$, and $x(t) = x_0 + \int_{\tau_0}^{t} (A x(s) + b(s))\,ds$ for every $t \in [\tau_0, \tau_n]$;
- every switched trajectory $y$ agrees with $x$ on $[\tau_0, \tau_n]$.
