# Fuel-bounded Ulam test

For a natural number $f$ (the fuel) and a word $w$ in the letters
$0$ and $1$, the test returns false when $f = 0$. With fuel $f + 1$ it returns true when $w$ has
length $1$; otherwise it returns true exactly when there is exactly one $k$ with
$1 \le k < |w|$ such that the prefix $w_1 \cdots w_k$ and the suffix $w_{k+1} \cdots w_{|w|}$
are distinct and both pass the test with fuel $f$.

This is the Ulam recursion: with fuel at least $|w|$, the test decides whether $w$ is an Ulam
word.

## Sources

- Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma, *Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1 (definition of Ulam words, after Bade, Cui, Labelle, and Li).
