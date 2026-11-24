# Safety and co-safety properties are monitorable

Under the three-valued semantics of LTL on finite prefixes, every safety property and every co-safety property over a finite alphabet is monitorable: every finite prefix has an extension on which the verdict is definite. For a safety property $P$, a finite word is a *bad prefix* if none of its infinite extensions satisfies $P$; the verdict $\bot$ is reached exactly on the bad prefixes, and the prefixes that are not bad (those with some extension in $P$) form a prefix-closed regular language when $P$ is $\omega$-regular. A deterministic finite automaton for the non-bad prefixes is a monitor whose verdict on a finite word is $\bot$ exactly when the state it reaches is not accepting; for the empty property this already holds at the initial state. Non-bad prefixes differ from *good prefixes*, all of whose extensions satisfy $P$: the safety property $\mathbf{G}\,a$ has no good prefixes but has bad prefixes.

## Expansion

This page becomes ready once these prerequisites are stated:

- Three-valued semantics of LTL on finite prefixes (statement prerequisite)
- Safety-liveness decomposition (proof prerequisite)

## Sources

- A. Bauer, M. Leucker and C. Schallhart, "Runtime verification for LTL and TLTL", *ACM Transactions on Software Engineering and Methodology* 20(4), Article 14, 2011
