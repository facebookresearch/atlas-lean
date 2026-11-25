# Real soundness of a rational LP certificate check

Let $A \in \mathbb Q^{m \times n}$, $b \in \mathbb Q^m$, $c \in \mathbb Q^n$, $x \in \mathbb Q^n$, $y \in \mathbb Q^m$ and $\varepsilon \in \mathbb Q$, and suppose the exact rational check accepts: $x \ge 0$, $A x \le b$, $y \ge 0$, $A^\top y \ge c$ and $0 \le b \cdot y - c \cdot x \le \varepsilon$. Then the same relations hold for the real casts, and every real $z \ge 0$ with $A z \le b$ satisfies $c \cdot z \le c \cdot x + \varepsilon$.
