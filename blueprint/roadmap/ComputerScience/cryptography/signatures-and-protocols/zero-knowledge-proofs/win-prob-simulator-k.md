# The truncated rewinding simulator reproduces the real view

Under the hypotheses of [one rewinding attempt](win-prob-attempt-dist.md), for every verifier $V^*$,
every test $T$ of its view and every $k$, the [simulator with $k$ attempts](simulator-k.md) outputs a
view passing $T$ with probability exactly
$\bigl(1 - (1 - 1/\lvert \mathrm{Ch} \rvert)^k\bigr) \Pr[T \text{ holds of the real view}]$. By induction
on $k$: the first attempt succeeds and passes $T$ with probability $\Pr[T]/\lvert \mathrm{Ch} \rvert$ and
fails with probability $1 - 1/\lvert \mathrm{Ch} \rvert$, after which the remaining attempts are run
afresh.

## Informally uses

- [One rewinding attempt simulates the real view](win-prob-attempt-dist.md)
