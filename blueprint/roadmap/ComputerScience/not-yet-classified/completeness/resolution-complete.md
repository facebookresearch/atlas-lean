# Resolution Complete

Resolution complete (LaValle, Planning Algorithms, Ch. 5 introduction): sound,
and on every solvable problem some step finds a path.

The termination clause renders Ch. 5 introduction "if a solution exists, the
algorithm will find it in finite time" as existence of a finding step `k`; on
unsolvable problems the planner may answer `running` at every step (Ch. 5
introduction "may run forever"). This is the exists-`k` reading, not an
eventually-always reading.
