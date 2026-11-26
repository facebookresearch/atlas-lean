# Generalized noninterference is not preserved by hook-up

**Theorem (McCullough).** There are [rated event systems](rated-event-systems-and-level-views.md) $A$ and $B$ that both have
[generalized noninterference](generalized-noninterference.md) and whose [simple hook-up](event-systems-and-their-hook-up.md) does not.

In the witness, $A$ outputs the unclassified event $\mathit{stop\text{-}count}$ at any time and then $\mathit{even}$ or $\mathit{odd}$ according to the parity of its secret events before
$\mathit{stop\text{-}count}$, and may emit secret outputs at any time; $B$ behaves alike with $\mathit{stop\text{-}count}$ as an input and its secret outputs sent to $A$. Each component
repairs an added secret input by one more secret output, but in the composite each such output is a secret input to the other component, so no repair keeps both
parity reports unchanged.

## Depends on

- [Generalized noninterference](generalized-noninterference.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 8, Section 8.4.1 (a flaw in generalized noninterference), with Figures 8.11–8.20.
