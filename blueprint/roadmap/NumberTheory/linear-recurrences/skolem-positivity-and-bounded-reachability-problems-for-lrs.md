# Skolem, positivity and bounded reachability problems for LRS

An integer linear recurrence sequence of order $k \ge 1$ is given by integers $c_0, \dots, c_{k-1}$ and initial values
$u_0, \dots, u_{k-1}$, with $u_{n+k} = \sum_{i<k} c_i u_{n+i}$. The Skolem problem asks whether $u_n = 0$ for some $n$; the positivity
problem whether $u_n \ge 0$ for all $n$; the ultimate positivity problem whether $u_n \ge 0$ for all sufficiently large $n$. The
bounded Skolem problem, given in addition a horizon $N$, asks whether $u_n = 0$ for some $n \le N$; whether $N$ is given in unary
or binary is part of the problem. The matrix form, given an integer matrix $M$ and integer vectors $s$, $e$, asks whether
$e^{\mathsf T} M^n s = 0$ for some $n$; its correspondence with recurrences is a separate page. These are definitions; they
assert nothing about decidability.

## Expansion

This node states a precise definition. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: linear recurrence sequences and their matrix (observed linear dynamics) form.

## Sources

- The Skolem Landscape (Invited Talk) — J. Worrell, ICALP 2023, LIPIcs 261, 5:1-5:2, DOI 10.4230/LIPIcs.ICALP.2023.5. <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.5> Abstract.
