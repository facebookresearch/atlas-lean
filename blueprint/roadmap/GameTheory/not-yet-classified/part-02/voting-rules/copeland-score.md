# Copeland score

For finitely many alternatives and finitely many voters with strict rankings, the Copeland score of an alternative $a$ is the number of alternatives $b$ that $a$ beats by pairwise majority (strictly more than half of the voters prefer $a$ to $b$) minus the number of alternatives that beat $a$ by pairwise majority.

SECOND-ORDER COPELAND MANIPULATION uses this function unchanged: its `copelandScore` is a wrapper whose body is exactly this score.
