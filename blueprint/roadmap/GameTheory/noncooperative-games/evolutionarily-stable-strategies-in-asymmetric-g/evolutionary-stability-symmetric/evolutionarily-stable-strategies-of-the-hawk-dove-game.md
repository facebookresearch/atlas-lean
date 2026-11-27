# Evolutionarily stable strategies of the Hawk–Dove game

In the Hawk–Dove game with resource value $V > 0$ and injury cost $C > 0$ (Hawk vs Hawk yields $(V - C)/2$, Hawk vs Dove yields $V$ and $0$, Dove vs Dove yields $V/2$ each), if $V < C$ the mixed strategy that plays Hawk with probability $V/C$ is an evolutionarily stable state, and if $V \ge C$ pure Hawk is an evolutionarily stable state.

## Proof sketch

For $V < C$ the mixed strategy with Hawk probability $V/C$ equalizes the payoffs of Hawk and Dove, and the second-order condition holds because, with $F(s \mid t) = s \cdot A t$, $F(t\mid t) - F(s\mid t)$ is a negative multiple of $(t_H - V/C)^2$. For $V \ge C$ Hawk is a strict or weak best response satisfying the second-order condition.

These states are the only evolutionarily stable states, since an evolutionarily stable state is a symmetric Nash equilibrium. Against a population playing Hawk with probability $q$, Hawk earns $q(V-C)/2 + (1-q)V$ and Dove earns $(1-q)V/2$, so Hawk minus Dove is $(V - qC)/2$. If $V < C$, pure Dove is not a best reply to itself (the difference is $V/2 > 0$), pure Hawk is not (the difference is $(V-C)/2 < 0$), and a fully mixed equilibrium needs $q = V/C$. If $V \ge C$, the difference is positive for every $q < 1$, so Hawk is the only best reply to any other strategy and pure Hawk is the only symmetric equilibrium.

More generally, a symmetric game with $2 \times 2$ payoff matrix $A$ has an evolutionarily stable state whenever $a = A_{11} - A_{21} \ne 0$ and $b = A_{22} - A_{12} \ne 0$. If $a > 0$, the first pure strategy is a strict best reply to itself and hence evolutionarily stable; if $b > 0$, so is the second. If $a < 0$ and $b < 0$, let $t$ play the first strategy with probability $p^* = b/(a+b) \in (0, 1)$; against a strategy $s$ playing it with probability $q$, the first strategy earns $a q - b(1-q) = (a+b)(q - p^*)$ more than the second, so $t$ makes both pure strategies equally good and every $s$ is a best reply to $t$, while $F(t \mid s) - F(s \mid s) = (p^* - q)(a+b)(q - p^*) = -(a+b)(q-p^*)^2 > 0$ for $s \ne t$, which is the second-order condition.

## Depends on

- [Evolutionarily stable state of a matrix game](../../../../Biology/population-dynamics/stability-of-evolutionarily-stable-states/is-ess.md)

## Proof depends on

- [Evolutionarily stable strategies refine symmetric Nash equilibria](evolutionarily-stable-strategies-refine-symmetric-nash-equilibria.md)

## Sources

- Siddharth Suri, "Computational Evolutionary Game Theory", Algorithmic Game Theory, Cambridge University Press, 2007, Section 29.1 (Figure 29.1, the Hawks and Doves game; pure Hawk is an ESS when $V > C$; Definition 29.1 and Theorem 29.2) and Exercise 29.2 (the mixed strategy playing Hawk with probability $V/C$ is an ESS when $V \le C$).
