# Compliance error with supplied model, discretization, solver and arithmetic terms

Let $J(F, k) = F \cdot (F/k)$ be the compliance of a spring of stiffness $k$ under end force $F$. Let $k_{\min} > 0$, $|F| \le F_{\max}$, $|\hat F| \le F_{\max}$, $k \ge k_{\min}$ and $\hat k \ge k_{\min}$. Let $J_{\mathrm{model}}, J_{\mathrm{disc}}, J_{\mathrm{solve}}, J_{\mathrm{comp}}$ be real numbers with

$$|J(\hat F, \hat k) - J_{\mathrm{model}}| \le e_{\mathrm{model}},\quad |J_{\mathrm{model}} - J_{\mathrm{disc}}| \le e_{\mathrm{disc}},\quad |J_{\mathrm{disc}} - J_{\mathrm{solve}}| \le e_{\mathrm{solve}},\quad |J_{\mathrm{solve}} - J_{\mathrm{comp}}| \le e_{\mathrm{arith}}.$$

Then

$$|J(F, k) - J_{\mathrm{comp}}| \le \frac{2F_{\max}}{k_{\min}}|F - \hat F| + \frac{F_{\max}^2}{k_{\min}^2}|k - \hat k| + e_{\mathrm{model}} + e_{\mathrm{disc}} + e_{\mathrm{solve}} + e_{\mathrm{arith}}.$$
