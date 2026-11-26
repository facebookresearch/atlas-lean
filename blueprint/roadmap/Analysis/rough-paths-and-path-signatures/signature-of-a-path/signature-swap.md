# Reversing the orientation of the interval

Let every component of the velocity of $X$ be continuous. For all reals $a, b$ and every word,

$$S(X)^{i_1 \cdots i_k}_{b,a} = (-1)^k\, S(X)^{i_k \cdots i_1}_{a,b}.$$

The proof is induction on the word: integrating the last letter from $b$ back to $a$ and using
the [first-letter recursion](signature-cons.md) for the reversed word.
