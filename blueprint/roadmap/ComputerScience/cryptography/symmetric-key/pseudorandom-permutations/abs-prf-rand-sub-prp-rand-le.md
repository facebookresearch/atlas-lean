# Switching lemma for distinguishers with uniform coins

Let $X$ be a finite nonempty set and let a distinguisher with uniform coins make at most $q$ queries
for every value of its coins. It tells a uniformly random function $X \to X$ from a uniformly random
permutation of $X$ with advantage at most the probability that $q$ independent uniform samples from
$X$ are not all distinct (Bellare and Rogaway, Lemma 1; Boneh and Shoup, Theorem 4.4). For each
fixed value of the coins the bound holds by the switching lemma for a deterministic distinguisher.
Over uniform coins each success probability is the average of the success probabilities for fixed
coins, so the advantage is at most the average of the advantages for fixed coins.
