# Occupied iff lt roster card

In a stable partial matching of finitely many students to college copies, slot `(c,i)` is
occupied exactly when `i` is smaller than the number of students assigned to `c` after collapse.
Each student ranks the copies consecutively where `c` stood relative to other colleges and being
unmatched, always preferring the smaller index. Each copy inherits `c`'s strict ranking of
students and an empty seat. The cutoff includes empty and full rosters; at quota zero there is
no slot index.
