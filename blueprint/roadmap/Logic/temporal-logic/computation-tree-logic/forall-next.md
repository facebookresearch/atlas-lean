# The CTL operator $\mathsf{AX}$

For a CTL formula $\varphi$, the formula
$\mathsf{AX}\,\varphi$ ("on all next states, $\varphi$") is defined as
$\neg\,\mathsf{EX}\,\neg\varphi$.

It holds at a state exactly when every successor of that state satisfies $\varphi$, so it holds
vacuously at a deadlocked state.
