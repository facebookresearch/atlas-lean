# The switching lemma

**The switching lemma** (Bellare and Rogaway, Lemma 1; Boneh and Shoup, Theorem 4.4): a
distinguisher with uniform coins making at most `q` queries tells a random function from a random
permutation with advantage at most `collisionProb X q`. For each fixed coin value this is
`Cslib.Crypto.Framework.LazySampling.switching_lemma`; the advantage over uniform coins is the
average of those advantages.
