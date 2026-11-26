# Previous writes in an x86-TSO event structure

For a relation $\prec$ on events and an
event $e$, the previous writes are the writes $w$ with $w \prec e$ whose location is that of $e$
(Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3.2, `previous_writes`).
