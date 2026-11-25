# Nash equilibrium of a bimatrix game

Let $M$ and $N$ be finite sets of pure strategies of players 1 and 2, and let $\Delta(M)$ and $\Delta(N)$ be their sets of mixed strategies (probability vectors).
For payoff matrices $A, B \in \mathbb{R}^{M \times N}$, the pair $(x, y) \in \Delta(M) \times \Delta(N)$ is
a Nash equilibrium of the game $(A, B)$ if $x$ maximises player 1's expected payoff against $y$ and $y$
maximises player 2's expected payoff against $x$: $x'^{\mathsf T} A y \le x^{\mathsf T} A y$ for every
$x' \in \Delta(M)$ and $x^{\mathsf T} B y' \le x^{\mathsf T} B y$ for every $y' \in \Delta(N)$
(von Stengel, *Algorithmic Game Theory*, Section 3.2).
