# Stage Transition LE

The stage map attached to a proof `i <= j`.  Its computational offset is
literally `j-i`; the result is transported into stage `j` by
`Nat.add_sub_of_le`.
