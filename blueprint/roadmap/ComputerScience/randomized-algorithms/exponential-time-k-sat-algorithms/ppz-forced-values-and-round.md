# Forced values and the PPZ round

Let $\varphi$ be a CNF formula on $x_1, \dots, x_n$ and $\tau$ a partial assignment. A variable $x$ unset in $\tau$ is **forced to $b$** if some clause of $\varphi$ contains the literal $x = b$, every other literal of that clause is falsified by $\tau$, and the clause contains no literal on $x$ of the opposite polarity; it then has the **forced value** $b$ (if both polarities are forced, the polarity $1$ is used).

One **PPZ round** draws a uniformly random ordering $\pi$ of the variables (lazily, by a Fisher-Yates shuffle) and processes the variables in that order, setting each to its forced value under the current partial assignment if it has one and to a uniformly random bit otherwise. The round **succeeds** if the resulting total assignment satisfies $\varphi$.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [Fisher–Yates shuffle with supplied draws](../fisher-yates-shuffle/randomly-permute.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", 38th IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
