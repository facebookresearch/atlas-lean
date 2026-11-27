# Root limit of the full Cohn–Elkies bound

As the integer dimension $d$ tends to infinity, the positive-dimensional real roots satisfy $B_d^{1/d}\to\sqrt{e/(2\pi)}$. Equivalently, for some real sequence $e_d\to0$, eventually $B_d=(\sqrt{e/(2\pi)}+e_d)^d$.

## Depends on

- [Full Cohn–Elkies linear-programming bound](full-cohn-elkies-linear-program.md)

## Proof depends on

- [Asymptotic infimum of rooted Cohn–Elkies quotients](asymptotic-quotient-root.md)

## Expansion

Combine the rooted quotient limit with the unit-ball volume asymptotic (Stirling) and justify commuting positive roots with the infimum. Raise the eventual positive roots back to the dimension power to obtain the error form.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 1](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `exact_limit`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L145-L150)
- [Pinned source: `sharpFullCohnElkiesManuscriptConclusions`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L179-L180)
