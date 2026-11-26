# Primitive blocks of the diagram compiler

The primitive blocks of the IMP diagram compiler, typed by their input and output wires: `skip` and an assignment from one state wire to one state wire, a branch on a guard from one state wire to two (the left wire for false, the right for true), and a join from two state wires to one. Composite commands are not atoms; they are built from these by sequencing, tensor and feedback.
