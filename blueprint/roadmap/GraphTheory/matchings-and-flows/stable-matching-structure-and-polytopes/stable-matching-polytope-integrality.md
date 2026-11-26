# Vande Vate-Rothblum: the stable matching polytope is integral

The fractional stable matching polytope equals the convex hull of the incidence matrices of stable matchings, and its extreme points are exactly these $0/1$ matrices.

## Proof sketch

Teo-Sethuraman threshold rounding: for a fractional point $x$ and a uniform threshold $\theta \in (0,1)$, match each proposer to the receiver whose cumulative preference interval (in the proposer's order) contains $\theta$; the stability constraints make this a stable matching, and averaging over $\theta$ recovers $x$.

## Depends on

- [The fractional stable matching polytope](fractional-stable-matching-polytope.md)

## Sources

- J. H. Vande Vate, "Linear Programming Brings Marital Bliss", Operations Research Letters 8(3), 1989.
- U. G. Rothblum, "Characterization of Stable Matchings as Extreme Points of a Polytope", Mathematical Programming 54, 1992.
- C.-P. Teo and J. Sethuraman, "The Geometry of Fractional Stable Matchings and Its Applications", Mathematics of Operations Research 23(4), 1998.
