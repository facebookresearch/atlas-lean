# Second-order Copeland score

For a profile of voter preferences over finitely many alternatives, the Copeland score of an alternative is the number of alternatives it beats by pairwise majority minus the number that beat it. The second-order Copeland score of $a$ is the sum of the Copeland scores of the alternatives that $a$ beats by pairwise majority.

SECOND-ORDER COPELAND MANIPULATION uses this function unchanged: its `secondOrderScore` is a wrapper whose body is exactly this score.
