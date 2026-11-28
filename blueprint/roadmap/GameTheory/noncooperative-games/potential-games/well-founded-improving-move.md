# Finite improvement property

In a game with finitely many strategy profiles and an exact potential, the improving-move
relation is well founded: there is no infinite sequence of profiles each reached from the previous
one by an improving move. In particular best-response dynamics, from any starting profile,
reaches a pure Nash equilibrium after finitely many steps.

Equivalently, in an exact-potential game with finitely many players and finite strategy sets there is no infinite sequence of profiles in which each step is a strict unilateral cost improvement (`no_infinite_improvement_path`): the profile type is finite and each step is an improving move.

## Informally uses

- [Improving moves decrease the potential](lt-of-improving-move.md): the potential strictly
  decreases along an improvement path, and takes finitely many values.

## Sources

- D. Monderer and L. S. Shapley, "Potential games", Games Econom. Behav. 14 (1996), 124–143, Lemma 2.3.
- J. Kleinberg and É. Tardos, *Algorithm Design*, Addison-Wesley, 2005, §12.7.
