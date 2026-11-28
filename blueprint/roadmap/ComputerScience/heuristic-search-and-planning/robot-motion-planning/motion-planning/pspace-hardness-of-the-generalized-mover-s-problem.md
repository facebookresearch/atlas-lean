# PSPACE-hardness of the generalized mover's problem

This node collects PSPACE-hardness results for motion planning, each for its own model and encoding.

## Expansion

A sound expansion has separate pages for:

1. **Linked polyhedral bodies** (Reif 1979): deciding whether a robot of finitely many polyhedral bodies joined at spherical
   joints can move between two configurations among polyhedral obstacles, with rational coordinates, is PSPACE-hard; the
   reduction simulates a symmetric Turing machine by dangling robot parts moving through a system of tunnels.
2. **Warehouseman's problem:** coordinated translation of axis-aligned rectangles in a rectangular region is PSPACE-hard.
3. **Sokoban** is PSPACE-hard, with its puzzle encoding.
4. **Planar linkages:** motion planning for a chain of bodies in the plane is PSPACE-hard, as stated in its source.

Each result has its own reduction; one survey summary does not make the models interchangeable.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Polynomial-time many-one (Karp) reduction.

## Depends on

- [Semi-algebraic motion planning instances and input size](semi-algebraic-motion-planning-instances-and-input-size.md)
- [Polynomial space for decision problems](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- Planning Algorithms, web section 'Lower bounds for motion planning' (Ch. 6 computational complexity) — S. M. LaValle, Planning Algorithms, Lower bounds for motion planning (node303), Sec. 6.5.1. <https://lavalle.pl/planning/node303.html>
- MIT 16.410 Principles of Autonomy and Decision Making, Lecture 15: Sampling-Based Algorithms for Motion Planning, Generalized Piano Mover's problem PSPACE-hard [Reif '79]. <https://opencw.aprende.org/courses/aeronautics-and-astronautics/16-410-principles-of-autonomy-and-decision-making-fall-2010/lecture-notes/MIT16_410F10_lec15.pdf>
