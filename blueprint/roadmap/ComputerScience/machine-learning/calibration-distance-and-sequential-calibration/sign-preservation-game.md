# The sign-preservation game

The **sign-preservation game with reuse** (SPR) with parameters $n, s \in \mathbb{N}$ is played between Player-P (the pointer) and Player-L (the labeler) on $n$ cells numbered $1, \dots, n$, initially empty. The game lasts at most $s$ rounds. In each round:

1. Player-P may terminate the game; otherwise it points at an empty cell $j \in [n]$.
2. Knowing $j$, Player-L may remove any of the minus signs in cells to the left of $j$ and any of the plus signs in cells to the right of $j$.
3. Player-L places a sign, $+$ or $-$, into cell $j$.

Player-P maximizes, and Player-L minimizes, the number of signs remaining at the end; both may randomize, and $\mathrm{opt}(n, s)$ is the optimal expected number of remaining signs. The **sign-preservation game** of Qiao and Valiant is the special case in which Player-P points at each cell at most once and Player-L removes every sign it is allowed to remove. In the sign-preservation game a $+$ sign is preserved exactly when every later sign is placed in a cell with a larger number, and a $-$ sign exactly when every later sign is placed in a cell with a smaller number. Upper bounds on $\mathrm{opt}(n,n)$ translate into forecasters with small $\ell_1$ calibration error, and lower bounds on $\mathrm{opt}(n, n^\alpha)$ into lower bounds on the minimax $\ell_1$ calibration error.

## Sources

- M. Qiao, G. Valiant, "Stronger Calibration Lower Bounds via Sidestepping", STOC (2021), arXiv:2012.03454.
- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, R. Kleinberg, P. Okoroafor, "Breaking the T^{2/3} Barrier for Sequential Calibration", STOC (2025), arXiv:2406.13668.
