# TreeNash computes and represents all Nash equilibria of tree graphical games

For a finite graphical game on a tree in which every player has two actions, the TreeNash dynamic program over exact mixed strategies outputs a mixed Nash equilibrium, and a mixed profile is a Nash equilibrium of the game if and only if it is consistent with the computed tables, i.e. can be produced by the upstream pass for some choice of witnesses.

## Proof sketch

By induction on subtrees, $T(w, v)(x_w, x_v)$ holds iff the subtree rooted at $v$ has a profile, extending $x_v$, that is an equilibrium of the subtree game when $w$ is frozen at $x_w$. Nonemptiness at the root follows from Nash's theorem applied to the whole game.

## Depends on

- [TreeNash two-pass dynamic program](treenash-two-pass-dynamic-program.md)
- [Mixed Nash equilibrium](../is-mixed-nash.md)

## Proof depends on

- [Nash's theorem](../exists-is-mixed-nash.md)

## Sources

- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007, Section 7.2 (binary actions) and Theorem 7.3 (TreeNash computes a Nash equilibrium, and its tables and witness lists represent all Nash equilibria).
