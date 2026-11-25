# Time and space bounds for alignment dynamic programs

This node collects the cost contracts of the dynamic-programming algorithms for pairwise sequence alignment, for
sequences $x$ and $y$ of lengths $m$ and $n$, counting table-cell updates under unit-cost arithmetic.

## Expansion

A sound expansion has separate pages for:

1. **Score only.** The optimal global (Needleman–Wunsch) and local (Smith–Waterman) alignment scores with linear gap
   costs (one table), and the optimal global score with affine gap costs (Gotoh's three tables), are computed with
   $\Theta(mn)$ cell updates of constant cost each, keeping $O(\min(m, n))$ cells.
2. **Reconstruction.** Hirschberg's divide-and-conquer algorithm reconstructs an optimal alignment with $O(\min(m,n))$
   working space beyond the output (and $O(m + n)$ including it), using at most about twice the $mn$ cell updates of
   one full table under the counting convention stated on the page.
3. **Affine gaps with reconstruction,** as its own statement.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Related topics

- [The Smith–Waterman table](sequence-alignment/smith-waterman-local-alignment/sw-tab.md)
- [The table computes the optimal local alignment score](sequence-alignment/smith-waterman-local-alignment/sw-tab-eq-local-score.md)
- [The Gotoh table](sequence-alignment/gotoh-affine-gap-alignment/gotoh-tab.md)
- [Hirschberg's alignment algorithm](sequence-alignment/hirschberg-s-linear-space-alignment/hirschberg.md)

## Sources

- MIT 18.417 Introduction to Computational Molecular Biology (Fall 2004), Readings — MIT OpenCourseWare (readings from Jones & Pevzner, An Introduction to Bioinformatics Algorithms, MIT Press 2004). <https://ocw.mit.edu/courses/18-417-introduction-to-computational-molecular-biology-fall-2004/pages/readings/> Lecture 7, More Efficient Alignment (reading: Chapter 7).
