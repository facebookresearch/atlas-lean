# The firing map expands

Let `f` and `g` satisfy the hypotheses of Section 2.1
(`StateFunction`: `f` smooth on `[0, 1]` with `f(0) = 0`, `f(1) = 1`, `f' > 0`, `f'' < 0`, and `g`
its inverse), let `ε > 0` and `0 < φ < 1`, and assume no absorption, `f(1 - φ) + ε < 1`. Then the
firing map `h = firingMap f g ε` has a derivative `d` at `φ` with `d < -1`.

The value of the derivative and the place of `h(φ)` are facts of the source's proof of Lemma 2.1,
not part of this statement: its Eq. (2.3) gives `h'(φ) = -g'(ε + f(1 - φ)) / g'(f(1 - φ))`, which
is `-f'(1 - φ) / f'(h(φ))` since `g' = 1 / (f' ∘ g)`, and there `h(φ) = g(ε + f(1 - φ))` lies in
`(1 - φ, 1)` because `g` is increasing, `ε > 0` and `ε + f(1 - φ) < 1`.

## Sources

- R. E. Mirollo and S. H. Strogatz, "Synchronization of pulse-coupled biological oscillators", SIAM J. Appl. Math. 50 (1990) 1645–1662, Section 2.4, Lemma 2.1.
