# The regression play

Write $\ast$ for the unique world, and consider the game positions
(formula, world, binder stack listed innermost first)
$P_0 = (\mu X.\,\nu Y.\,X,\ \ast,\ [\,])$, $P_1 = (\nu Y.\,X,\ \ast,\ [\mu X.\,\nu Y.\,X])$ and
$P_2 = (X,\ \ast,\ [\nu Y.\,X,\ \mu X.\,\nu Y.\,X])$. Let $s$ be the step map sending $P_0$ to
$P_1$, $P_1$ to $P_2$ and $P_2$ to $P_0$, and fixing every other position. The regression play is
the sequence of positions $p_0 = P_0$, $p_{n+1} = s(p_n)$, which cycles through $P_0, P_1, P_2$.

These are the successive positions of the model-checking game for $\mu X.\,\nu Y.\,X$ on the
one-world model.
