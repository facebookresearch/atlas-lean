# Evaluation frames

One layer of an evaluation context: the function or argument
position of an application, the left or right operand of a multiplication, the test of `ifz`,
and the argument of `callcc`. There is no frame for `abort`, whose argument is not evaluated.
