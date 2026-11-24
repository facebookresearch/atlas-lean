/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.RealSumProductExponent

namespace MathlibExt.Combinatorics.RealSumProductExponentWanted

/--
**The Erdős–Szemerédi conjecture fails for real sets.** For a finite set $A \subset \mathbb{R}$
write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products $ab$ with $a, b \in A$,
and let the real sum-product exponent $C_{84b}$ be the limit inferior, as $n \to \infty$, of the
least value of $\log \max(|A + A|, |AA|) / \log n$ over sets $A \subset \mathbb{R}$ with
$|A| = n$. Then $C_{84b} \ne 2$.

Bloom, Sawin, Schildkraut and Zhelezov construct arbitrarily large finite sets
$A \subset \mathbb{R}$ with $\max(|A + A|, |AA|) \le |A|^{2 - c}$ for an absolute constant $c > 0$,
so $C_{84b} \le 2 - c$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of
integers, Studies in Pure Mathematics (1983), 213-218,
https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products,
Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József
Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37
(2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding
multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted erdosSzemerediHistoricalConjecture_refuted :
    ¬ erdosSzemerediHistoricalConjecture

/--
**The real sum-product exponent is less than 2 (Bloom–Sawin–Schildkraut–Zhelezov).** The real
sum-product exponent $C$ satisfies $C < 2$. Here, for a finite set $A \subset \mathbb{R}$,
$A + A$ and $A \cdot A$ are the sets of sums $a + b$ and products $ab$ with $a, b \in A$, and
$M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$ is the minimum of
$\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

This refutes the historical Erdős–Szemerédi conjecture $C = 2$ for real sets: Bloom, Sawin,
Schildkraut and Zhelezov (arXiv:2605.28781) construct arbitrarily large finite sets
$A \subset \mathbb{R}$ with $M(A) \le |A|^{2 - c}$ for an absolute constant $c > 0$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomSawinSchildkrautZhelezovRefutation_holds :
    bloomSawinSchildkrautZhelezovRefutation

/--
**Bloom–Sawin–Schildkraut–Zhelezov upper bound for the real sum-product exponent.** There is a
real number $c > 0$ such that the real sum-product exponent $C$ satisfies $C \le 2 - c$. Here,
for a finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$ are the sets of sums $a + b$
and products $ab$ with $a, b \in A$, and $M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$,
$m(n)$ is the minimum of $\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with
$|A| = n$; and $C = \liminf_{n \to \infty} m(n)$.

Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781) construct arbitrarily large finite
sets $A \subset \mathbb{R}$ with $M(A) \le |A|^{2 - c}$ for an absolute constant $c > 0$;
Optimization Problems 84b lists the resulting upper bound $2 - c$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomSawinSchildkrautZhelezovUpperBound_holds :
    bloomSawinSchildkrautZhelezovUpperBound

/--
**Bloom–Sawin–Schildkraut–Zhelezov numerical upper bound for the real sum-product exponent.** The
real sum-product exponent $C$ satisfies $C \le 199999913/100000000 = 1.99999913$. Here, for a
finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$ are the sets of sums $a + b$ and
products $ab$ with $a, b \in A$, and $M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$
is the minimum of $\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

Bloom, Sawin, Schildkraut and Zhelezov sketch, in the section "Numerical estimates" of
arXiv:2605.28781, a quantified version of their construction that gives arbitrarily large finite
sets $A \subset \mathbb{R}$ with $M(A) \le |A|^{2 - 0.00000087}$; they call this value
non-optimized. Optimization Problems 84b lists it as the explicit upper bound $1.99999913$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomSawinSchildkrautZhelezovNumericalUpperBound_holds :
    bloomSawinSchildkrautZhelezovNumericalUpperBound

/--
**Elekes's lower bound for the real sum-product exponent.** For a finite set $A \subset \mathbb{R}$
write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products $ab$ with $a, b \in A$,
and let the real sum-product exponent $C_{84b}$ be the limit inferior, as $n \to \infty$, of the
least value of $\log \max(|A + A|, |AA|) / \log n$ over sets $A \subset \mathbb{R}$ with
$|A| = n$. Then $C_{84b} \ge 5/4$.

Elekes proved, using the Szemerédi–Trotter theorem, that $\max(|A + A|, |AA|) \gg |A|^{5/4}$ for
finite sets $A \subset \mathbb{R}$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers,
Studies in Pure Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19;
György Elekes, On the number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted elekesLowerBound_holds : elekesLowerBound

/--
**Solymosi's $14/11$ lower bound for the real sum-product exponent.** Let $C$ be the real
sum-product exponent: the limit inferior, as $n \to \infty$, of the least value of
$\log \max(|A + A|, |AA|) / \log |A|$ over $n$-element sets $A \subset \mathbb{R}$, where
$A + A$ and $AA$ are the sets of sums $a + b$ and products $ab$ of elements $a, b \in A$. Then
$C \ge 14/11$.

Optimization Problems 84b lists the lower bound $14/11$ [So05] (Solymosi, Bull. London Math.
Soc. 37 (2005)); Bloom's history lists Solymosi 2005 with exponent $1 + 3/11$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers,
Studies in Pure Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19;
György Elekes, On the number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted solymosiFourteenEleventhsLowerBound_holds :
    solymosiFourteenEleventhsLowerBound

/--
**Rudnev–Stevens lower bound for the real sum-product exponent.** Let $C$ be the real
sum-product exponent: the limit inferior, as $n \to \infty$, of the least value of
$\log \max(|A + A|, |AA|) / \log |A|$ over $n$-element sets $A \subset \mathbb{R}$, where
$A + A$ and $AA$ are the sets of sums $a + b$ and products $ab$ of elements $a, b \in A$. Then
$C \ge 1558/1167$.

Rudnev and Stevens (arXiv:2005.11145, abstract) prove
$\max(|A + A|, |AA|) \ge |A|^{4/3 + 2/1167 - o(1)}$ for finite $A \subset \mathbb{R}$, and
$4/3 + 2/1167 = 1558/1167$; Optimization Problems 84b lists this bound [RuSt22].

Source: Paul Erdős and Endre Szemerédi,
On sums and products of integers, Studies in Pure Mathematics (1983), 213-218,
https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products,
Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József
Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37
(2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding
multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted rudnevStevensLowerBound_holds : rudnevStevensLowerBound

/--
**Bloom's lower bound for the real sum-product exponent.** The real sum-product exponent $C$ is
at least $1270/951$. Here, for a finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$ are
the sets of sums $a + b$ and products $ab$ with $a, b \in A$, and
$M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$ is the minimum of
$\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

Optimization Problems 84b lists this lower bound as Bloom 2025; Bloom's history of the
sum-product problem attributes it to Bloom, Control and its applications in additive
combinatorics. It also follows from Cushman's larger lower bound $4/3 + 10/4407$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomLowerBound_holds : bloomLowerBound

/--
**Cushman's lower bound for the real sum-product exponent.** The real sum-product exponent $C$ is
at least $4/3 + 10/4407$. Here, for a finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$
are the sets of sums $a + b$ and products $ab$ with $a, b \in A$, and
$M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$ is the minimum of
$\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

Cushman (arXiv:2512.13849) proves $M(A) \gg_\varepsilon |A|^{4/3 + 10/4407 - \varepsilon}$ for
every finite $A \subset \mathbb{R}$; Optimization Problems 84b lists this as the current record.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted cushmanCurrentLowerBound_holds : cushmanCurrentLowerBound

end MathlibExt.Combinatorics.RealSumProductExponentWanted
